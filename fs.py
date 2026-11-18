"""
fs.py — PARTE 2: camada de arquivos e diretórios do mini exFAT

Gerencia diretórios, arquivos, caminhos e entradas de diretório exFAT
- File Directory Entry (0x85)
- Stream Extension Directory Entry (0xC0)
- File Name Directory Entry (0xC1)

Layout das entradas (32 bytes cada):

    File (0x85):    +0 tipo | +1 SecondaryCount | +2..3 SetChecksum | +4..5 atributos
    Stream (0xC0):  +0 tipo | +1 flags (bit0 AllocationPossible, bit1 NoFatChain)
                    +3 NameLength (em caracteres UTF-16) | +4..5 NameHash
                    +8..15 ValidDataLength | +20..23 FirstCluster | +24..31 DataLength
    Name (0xC1):    +0 tipo | +1 flags | +2..31 até 15 caracteres UTF-16
"""

import math
import struct
from volume import Volume, ErroVolume, PRIMEIRO_CLUSTER, FAT_FIM

# tipos de entradas de diretório no exFAT
TIPO_FILE = 0x85
TIPO_STREAM_EXT = 0xC0
TIPO_FILE_NAME = 0xC1
TAM_ENTRADA = 32

# atributos de arquivo
ATTR_READ_ONLY = 0x0001
ATTR_HIDDEN = 0x0002
ATTR_SYSTEM = 0x0004
ATTR_DIRECTORY = 0x0010
ATTR_ARCHIVE = 0x0020

# flags da Stream Extension
FLAG_ALLOC_POSSIBLE = 0x01
FLAG_NO_FAT_CHAIN = 0x02

NOME_MAX = 255
CARACTERES_PROIBIDOS = set('\\/:*?"<>|')


class ErroFS(ErroVolume):
    """Erro genérico da camada de sistema de arquivos."""


class ArquivoNaoEncontrado(ErroFS):
    """Arquivo ou diretório não encontrado."""


class JaExiste(ErroFS):
    """O arquivo ou diretório já existe."""


class NaoEhDiretorio(ErroFS):
    """O caminho informado não é um diretório."""


class EhDiretorio(ErroFS):
    """O caminho informado é um diretório (e não um arquivo)."""


class DiretorioNaoVazio(ErroFS):
    """Tentativa de remover diretório não vazio."""


class NomeInvalido(ErroFS):
    """Nome de arquivo/diretório inválido."""


# ---------------------------------------------------------------- utilitários
def _rotacao16(c: int, b: int) -> int:
    """Passo do checksum de 16 bits do exFAT: roda 1 bit à direita e soma o byte."""
    return ((((c & 1) << 15) | (c >> 1)) + b) & 0xFFFF


def checksum_set(bloco: bytes) -> int:
    """SetChecksum do exFAT: cobre todas as entradas do set, ignorando os
    bytes 2-3 da primeira (que são o próprio checksum)."""
    c = 0
    for i, b in enumerate(bloco):
        if i in (2, 3):
            continue
        c = _rotacao16(c, b)
    return c


def hash_nome(nome: str) -> int:
    """NameHash do exFAT. Simplificação: sem Up-case Table, usa str.upper()."""
    c = 0
    for b in nome.upper().encode("utf-16le"):
        c = _rotacao16(c, b)
    return c


def validar_nome(nome: str) -> None:
    """Rejeita nomes vazios, longos demais ou com caracteres proibidos."""
    if not nome or nome in (".", ".."):
        raise NomeInvalido(f"nome inválido: {nome!r}")
    if len(nome.encode("utf-16le")) // 2 > NOME_MAX:
        raise NomeInvalido(f"nome maior que {NOME_MAX} caracteres")
    if any(ch in CARACTERES_PROIBIDOS or ord(ch) < 32 for ch in nome):
        raise NomeInvalido(f"nome contém caractere proibido: {nome!r}")


class FileSystem:
    """Interface de alto nível para manipulação de arquivos e diretórios."""

    def __init__(self, vol: Volume):
        self.vol = vol

    def _ler_diretorio_clusters(self, cluster_inicial: int) -> bytearray:
        """Lê todos os clusters pertencentes a um diretório (Regra 1: raiz usa FAT)."""
        # a raiz e subdiretórios usam a cadeia da FAT
        cadeia = self.vol.get_chain(cluster_inicial)
        if not cadeia:
            return bytearray()
        return bytearray(self.vol.read_data(cadeia, len(cadeia) * self.vol.cluster_size))

    def _escrever_diretorio_clusters(self, cluster_inicial: int, dados: bytes) -> int:
        """Grava dados em um diretório, estendendo a cadeia se necessário."""
        nec = self.vol.clusters_needed(len(dados))
        cadeia = self.vol.get_chain(cluster_inicial)

        if len(cadeia) < nec:
            extra = nec - len(cadeia)
            # diretórios usam NoFatChain=False (cadeia na FAT, Regra 1)
            cadeia, _ = self.vol.extend_chain(cadeia, False, extra)
        elif len(cadeia) > nec:
            cadeia = self.vol.shrink_chain(cadeia, False, nec)

        self.vol.write_data(cadeia, dados)
        return cadeia[0] if cadeia else cluster_inicial

    def _parse_entradas(self, blob: bytes) -> list:
        """Interpreta as entradas de diretório válidas (Regra 2: ignora o que não é 0x85)."""
        entradas = []
        i = 0
        while i < len(blob):
            tipo = blob[i]
            if tipo == 0x00:  # Fim do diretório
                break

            # Regra 2: Apenas entradas 0x85 ativas (bit 7 ligado) representam arquivos/pastas válidos
            if tipo == TIPO_FILE:
                count_secondary = blob[i + 1]
                tamanho_set = (1 + count_secondary) * TAM_ENTRADA
                bloco = blob[i:i + tamanho_set]

                parsed = self._decodificar_file_set(bloco, i)
                if parsed:
                    entradas.append(parsed)
                i += tamanho_set
                continue

            i += TAM_ENTRADA
        return entradas

    def _decodificar_file_set(self, bloco: bytes, offset_no_dir: int) -> dict:
        """Decodifica um File Set (File + Stream Ext + File Names)."""
        if len(bloco) < 3 * TAM_ENTRADA:
            return None
        num_secondary = bloco[1]
        if len(bloco) != (1 + num_secondary) * TAM_ENTRADA:
            return None                       # set truncado
        if struct.unpack_from("<H", bloco, 2)[0] != checksum_set(bloco):
            return None                       # set corrompido (SetChecksum não confere)

        file_attrs = struct.unpack_from("<H", bloco, 4)[0]

        # Stream Extension
        off_stream = TAM_ENTRADA
        if bloco[off_stream] != TIPO_STREAM_EXT:
            return None
        flags_stream = bloco[off_stream + 1]
        no_fat_chain = bool(flags_stream & FLAG_NO_FAT_CHAIN)
        tam_nome = bloco[off_stream + 3]
        # CORREÇÃO: FirstCluster fica em +20 e DataLength em +24
        primeiro_cluster = struct.unpack_from("<I", bloco, off_stream + 20)[0]
        data_length = struct.unpack_from("<Q", bloco, off_stream + 24)[0]

        # File Names
        nome_bytes = bytearray()
        for idx in range(2, 1 + num_secondary):
            off_name = idx * TAM_ENTRADA
            if bloco[off_name] == TIPO_FILE_NAME:
                nome_bytes += bloco[off_name + 2:off_name + 32]

        # NameLength diz quantos caracteres UTF-16 do nome são válidos
        nome_completo = bytes(nome_bytes[:tam_nome * 2]).decode("utf-16le", errors="ignore")

        return {
            "name": nome_completo,
            "is_dir": bool(file_attrs & ATTR_DIRECTORY),
            "attributes": file_attrs,
            "first_cluster": primeiro_cluster,
            "data_length": data_length,
            "no_fat_chain": no_fat_chain,
            "offset_no_dir": offset_no_dir,
            "raw_size": len(bloco)
        }

    def _buscar(self, dir_cluster: int, nome: str):
        """Procura 'nome' (sem diferenciar maiúsculas) dentro de um diretório."""
        for e in self._parse_entradas(self._ler_diretorio_clusters(dir_cluster)):
            if e["name"].lower() == nome.lower():
                return e
        return None

    def listar_diretorio(self, caminho: str) -> list:
        """Lista o conteúdo de um diretório dado o seu caminho."""
        cluster, is_dir = self._resolver_caminho(caminho)
        if not is_dir:
            raise NaoEhDiretorio(f"'{caminho}' não é um diretório")
        blob = self._ler_diretorio_clusters(cluster)
        return self._parse_entradas(blob)

    def _resolver_caminho(self, caminho: str) -> tuple:
        """Resolve um caminho absoluto para (cluster_inicial_ou_arquivo, is_dir)."""
        partes = [p for p in caminho.split("/") if p]
        cluster_atual = self.vol.root_cluster

        if not partes:
            return cluster_atual, True

        for i, parte in enumerate(partes):
            blob = self._ler_diretorio_clusters(cluster_atual)
            entradas = self._parse_entradas(blob)

            encontrado = None
            for e in entradas:
                if e["name"].lower() == parte.lower():
                    encontrado = e
                    break

            if not encontrado:
                raise ArquivoNaoEncontrado(f"Caminho não encontrado: {caminho}")

            if i == len(partes) - 1:
                return encontrado["first_cluster"], encontrado["is_dir"]

            if not encontrado["is_dir"]:
                raise NaoEhDiretorio(f"'{parte}' não é um diretório")

            cluster_atual = encontrado["first_cluster"]

        return cluster_atual, True

    def _resolver_diretorio(self, caminho: str) -> int:
        """Resolve um caminho que OBRIGATORIAMENTE deve ser um diretório."""
        cluster, is_dir = self._resolver_caminho(caminho)
        if not is_dir:
            raise NaoEhDiretorio(f"'{caminho}' não é um diretório")
        return cluster

    def criar_diretorio(self, caminho: str) -> None:
        """Cria um novo diretório (mkdir)."""
        dir_path, nome = rsplit_path(caminho)
        validar_nome(nome)
        dir_cluster = self._resolver_diretorio(dir_path)

        if self._buscar(dir_cluster, nome):
            raise JaExiste(f"O diretório '{nome}' já existe.")

        # Aloca 1 cluster para o novo diretório
        clusters, _ = self.vol.alloc_clusters(1)
        novo_cluster = clusters[0]

        try:
            # Regra 3: alloc_clusters não zera. É preciso zerar o cluster do diretório!
            self.vol.write_cluster(novo_cluster, b"")
            # CORREÇÃO: alloc_clusters(1) NÃO escreve na FAT, mas diretórios são
            # lidos seguindo a FAT: o cluster precisa terminar em End Of Chain.
            self.vol.write_fat(novo_cluster, FAT_FIM)

            # No exFAT real o DataLength de um diretório é o tamanho da sua cadeia
            file_set = self._montar_file_set(nome, novo_cluster, self.vol.cluster_size,
                                             False, is_dir=True)
            self._inserir_no_diretorio(dir_cluster, file_set)
        except Exception:
            self.vol.free_clusters([novo_cluster])   # não deixa o cluster vazado
            raise

    def criar_arquivo(self, caminho: str, dados: bytes = b"") -> None:
        """Cria um novo arquivo com dados opcionais."""
        dir_path, nome = rsplit_path(caminho)
        validar_nome(nome)
        dir_cluster = self._resolver_diretorio(dir_path)

        if self._buscar(dir_cluster, nome):
            raise JaExiste(f"O arquivo '{nome}' já existe.")

        # Regra 4: Arquivo vazio usa FirstCluster = 0 e DataLength = 0
        clusters, no_fat_chain = [], True
        if dados:
            nec = self.vol.clusters_needed(len(dados))
            clusters, no_fat_chain = self.vol.alloc_clusters(nec)

        try:
            if clusters:
                self.vol.write_data(clusters, dados)

            primeiro_cluster = clusters[0] if clusters else 0
            tamanho = len(dados)

            file_set = self._montar_file_set(nome, primeiro_cluster, tamanho, no_fat_chain, is_dir=False)
            self._inserir_no_diretorio(dir_cluster, file_set)
        except Exception:
            if clusters:
                self.vol.free_clusters(clusters)     # não deixa clusters vazados
            raise

    def ler_arquivo(self, caminho: str) -> bytes:
        """Lê todo o conteúdo de um arquivo."""
        dir_path, nome = rsplit_path(caminho)
        dir_cluster = self._resolver_diretorio(dir_path)

        e = self._buscar(dir_cluster, nome) if nome else None
        if e is None:
            raise ArquivoNaoEncontrado(caminho)
        if e["is_dir"]:
            raise EhDiretorio(f"'{caminho}' é um diretório")
        if e["data_length"] == 0 or e["first_cluster"] == 0:
            return b""

        cadeia = self.vol.get_chain(e["first_cluster"], e["data_length"], e["no_fat_chain"])
        return self.vol.read_data(cadeia, e["data_length"])

    def apagar(self, caminho: str) -> None:
        """Apaga arquivo ou diretório (Regra 5: limpa bit 7 e libera clusters)."""
        dir_path, nome = rsplit_path(caminho)
        validar_nome(nome)                      # impede apagar "/" ou nome vazio
        dir_cluster = self._resolver_diretorio(dir_path)

        blob = self._ler_diretorio_clusters(dir_cluster)
        entradas = self._parse_entradas(blob)

        alvo = None
        for e in entradas:
            if e["name"].lower() == nome.lower():
                alvo = e
                break

        if not alvo:
            raise ArquivoNaoEncontrado(caminho)

        if alvo["is_dir"]:
            # Verifica se está vazio (ignorando entradas nulas ou apagadas)
            sub_entradas = self.listar_diretorio(caminho)
            if sub_entradas:
                raise DiretorioNaoVazio(f"O diretório '{caminho}' não está vazio.")

        # Libera os clusters de dados se houver
        # CORREÇÃO: diretório é tratado à parte (cadeia na FAT, sem depender do DataLength)
        cadeia = []
        if alvo["first_cluster"] > 0:
            if alvo["is_dir"]:
                cadeia = self.vol.get_chain(alvo["first_cluster"])
            elif alvo["data_length"] > 0:
                cadeia = self.vol.get_chain(alvo["first_cluster"], alvo["data_length"],
                                            alvo["no_fat_chain"])
        if cadeia:
            self.vol.free_clusters(cadeia)

        # Regra 5: Zera o bit 7 do tipo das entradas no diretório pai (invalida o set)
        off = alvo["offset_no_dir"]
        num_secondary = blob[off + 1]
        total_set = (1 + num_secondary) * TAM_ENTRADA

        for idx in range(0, total_set, TAM_ENTRADA):
            if blob[off + idx] != 0:
                blob[off + idx] &= ~0x80  # Ex: 0x85 vira 0x05, 0xC0 vira 0x40, etc.

        self._escrever_diretorio_clusters(dir_cluster, bytes(blob))

    def _montar_file_set(self, nome: str, primeiro_cluster: int, tamanho: int, no_fat_chain: bool, is_dir: bool) -> bytes:
        """Cria os blocos binários das entradas exFAT (File, Stream, Name)."""
        nome_utf16 = nome.encode("utf-16le")
        num_name_entries = math.ceil(len(nome_utf16) / 30)
        total_secondary = 1 + num_name_entries

        bloco = bytearray((2 + num_name_entries) * TAM_ENTRADA)

        # 1) File Directory Entry (0x85)
        bloco[0] = TIPO_FILE
        bloco[1] = total_secondary
        attrs = ATTR_DIRECTORY if is_dir else ATTR_ARCHIVE
        struct.pack_into("<H", bloco, 4, attrs)

        # 2) Stream Extension Directory Entry (0xC0)
        off_stream = TAM_ENTRADA
        bloco[off_stream] = TIPO_STREAM_EXT
        # CORREÇÃO: AllocationPossible (bit 0) + NoFatChain (bit 1)
        flags = FLAG_ALLOC_POSSIBLE | (FLAG_NO_FAT_CHAIN if no_fat_chain else 0x00)
        bloco[off_stream + 1] = flags
        # CORREÇÃO: NameLength é o nº de caracteres UTF-16, não o nº de entradas
        bloco[off_stream + 3] = len(nome_utf16) // 2
        struct.pack_into("<H", bloco, off_stream + 4, hash_nome(nome))   # NameHash
        # CORREÇÃO: layout real (ValidDataLength +8, FirstCluster +20, DataLength +24)
        struct.pack_into("<Q", bloco, off_stream + 8, tamanho)           # ValidDataLength
        struct.pack_into("<I", bloco, off_stream + 20, primeiro_cluster) # FirstCluster
        struct.pack_into("<Q", bloco, off_stream + 24, tamanho)          # DataLength

        # 3) File Name Directory Entries (0xC1)
        for idx in range(num_name_entries):
            off_name = (2 + idx) * TAM_ENTRADA
            bloco[off_name] = TIPO_FILE_NAME
            bloco[off_name + 1] = 0x00
            chunk = nome_utf16[idx * 30 : (idx + 1) * 30]
            bloco[off_name + 2 : off_name + 2 + len(chunk)] = chunk

        # SetChecksum por último, depois de todo o set estar montado
        struct.pack_into("<H", bloco, 2, checksum_set(bytes(bloco)))

        return bytes(bloco)

    def _inserir_no_diretorio(self, dir_cluster: int, file_set: bytes) -> None:
        """Adiciona um File Set no cluster do diretório pai (reaproveita slots livres ou expande)."""
        blob = self._ler_diretorio_clusters(dir_cluster)
        n = len(file_set) // TAM_ENTRADA

        # CORREÇÃO: procura 'n' slots CONSECUTIVOS livres. Antes, o set era gravado
        # no primeiro slot livre, podendo sobrescrever entradas vivas seguintes
        # ou ficar depois de um 0x00 (onde o parser nunca chega).
        pos, inicio_run, run, fim = None, 0, 0, len(blob)
        for i in range(0, len(blob), TAM_ENTRADA):
            t = blob[i]
            if t == 0x00:                 # fim do diretório: daqui em diante é livre
                fim = i
                break
            if not (t & 0x80):            # entrada apagada (bit 7 zerado)
                if run == 0:
                    inicio_run = i
                run += 1
                if run == n:
                    pos = inicio_run
                    break
            else:
                run = 0
        if pos is None:
            # um trecho de apagadas logo antes do fim também pode ser aproveitado
            pos = inicio_run if run else fim

        fim_set = pos + len(file_set)
        if fim_set > len(blob):
            blob.extend(bytes(fim_set - len(blob)))   # expande (a cadeia cresce ao gravar)
        blob[pos:fim_set] = file_set

        self._escrever_diretorio_clusters(dir_cluster, bytes(blob))


def rsplit_path(caminho: str) -> tuple:
    """Separa '/a/b/c.txt' em ('/a/b', 'c.txt')."""
    partes = [p for p in caminho.split("/") if p]
    if not partes:
        return "/", ""
    nome = partes[-1]
    dir_path = "/" + "/".join(partes[:-1])
    return dir_path, nome

# ========================= demonstração

if __name__ == "__main__":
    img = "teste_exfat.img"
    Volume.format(img, tamanho=8 * 1024 * 1024)

    with Volume(img) as vol:
        fs = FileSystem(vol)

        # Cria pastas e arquivos
        fs.criar_diretorio("/docs")
        fs.criar_arquivo("/docs/readme.txt", b"Bem-vindo ao mini exFAT!")

        # Lista o diretório raiz e /docs
        print("Raiz:", [e["name"] for e in fs.listar_diretorio("/")])
        print("Docs:", [e["name"] for e in fs.listar_diretorio("/docs")])

        # Lê o arquivo
        print("Conteúdo:", fs.ler_arquivo("/docs/readme.txt").decode())

        # Apaga o arquivo e depois o diretório
        fs.apagar("/docs/readme.txt")
        fs.apagar("/docs")
        print("Raiz após limpeza:", [e["name"] for e in fs.listar_diretorio("/")])