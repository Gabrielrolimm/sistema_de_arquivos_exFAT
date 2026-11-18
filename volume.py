"""
volume.py — PARTE 1: camada de volume do mini exFAT
====================================================

Simula um disco exFAT dentro de um arquivo de imagem (.img). Esta camada
cuida de TUDO que é "baixo nível":

  * Boot Region (boot sector + checksum) e a sua cópia de backup
  * FAT (File Allocation Table)
  * Allocation Bitmap (mapa de clusters livres/ocupados)
  * Cluster Heap (onde ficam os dados)
  * Flag VolumeDirty (detecção de desmontagem incorreta)

Ela NÃO sabe o que é arquivo ou diretório — isso é da Parte 2. Aqui só
existem clusters e cadeias de clusters.

Layout do disco (em setores de 512 bytes), igual ao exFAT real:

    setor 0        Boot sector principal
    setores 1-10   (Extended boot sectors — zerados nesta versão)
    setor 11       Boot checksum
    setores 12-23  Boot Region de BACKUP (cópia de 0-11)
    setor 24 ...   FAT
    depois da FAT  Cluster Heap (clusters numerados a partir de 2)
                     cluster 2...  -> Allocation Bitmap
                     em seguida    -> Diretório raiz

Simplificações em relação ao exFAT real: apenas uma FAT, sem Up-case Table
e sem setores estendidos de boot.
"""

import math
import os
import random
import struct

# ---------------------------------------------------------------- constantes
BYTES_POR_SETOR_SHIFT = 9            # 2^9 = 512 bytes por setor
BYTES_POR_SETOR = 1 << BYTES_POR_SETOR_SHIFT
SETORES_BOOT_REGION = 12             # boot + 10 estendidos + checksum
FAT_OFFSET_SETORES = 24              # FAT começa depois das duas Boot Regions

PRIMEIRO_CLUSTER = 2                 # no exFAT o heap começa no cluster 2
FAT_LIVRE = 0x00000000
FAT_RUIM = 0xFFFFFFF7
FAT_FIM = 0xFFFFFFFF                 # End Of Chain

FLAG_VOLUME_DIRTY = 0x0002           # bit 1 de VolumeFlags
TIPO_ENTRADA_BITMAP = 0x81           # entrada "Allocation Bitmap" no diretório raiz
TAM_ENTRADA_DIR = 32

# Offsets reais do boot sector do exFAT
OFF_VOLUME_FLAGS = 106
OFF_PERCENT_IN_USE = 112
FORMATO_CAMPOS_BOOT = "<QQIIIIIIHHBBBBB"   # campos a partir do byte 64


class ErroVolume(Exception):
    """Erro genérico da camada de volume."""


class EspacoInsuficiente(ErroVolume):
    """Não há clusters livres suficientes."""


# ---------------------------------------------------------------- utilitários
def checksum_boot(regiao: bytes) -> int:
    """Checksum da Boot Region (algoritmo da especificação exFAT).

    Os bytes 106-107 (VolumeFlags) e 112 (PercentInUse) são ignorados porque
    mudam durante o uso normal — assim marcar o volume como "sujo" não
    invalida o checksum.
    """
    c = 0
    for i, b in enumerate(regiao):
        if i in (106, 107, 112):
            continue
        c = (((c & 1) << 31) | (c >> 1)) + b
        c &= 0xFFFFFFFF
    return c


def _montar_boot_region(campos: dict) -> bytes:
    bs = bytearray(BYTES_POR_SETOR)
    bs[0:3] = b"\xEB\x76\x90"          # JumpBoot
    bs[3:11] = b"EXFAT   "             # FileSystemName
    struct.pack_into(
        FORMATO_CAMPOS_BOOT, bs, 64,
        0,                              # PartitionOffset
        campos["volume_length"],        # VolumeLength (setores)
        campos["fat_offset"],           # FatOffset (setores)
        campos["fat_length"],           # FatLength (setores)
        campos["heap_offset"],          # ClusterHeapOffset (setores)
        campos["cluster_count"],        # ClusterCount
        campos["root_cluster"],         # FirstClusterOfRootDirectory
        campos["serial"],               # VolumeSerialNumber
        0x0100,                         # FileSystemRevision 1.00
        0,                              # VolumeFlags
        BYTES_POR_SETOR_SHIFT,          # BytesPerSectorShift
        campos["spc_shift"],            # SectorsPerClusterShift
        1,                              # NumberOfFats
        0x80,                           # DriveSelect
        0xFF,                           # PercentInUse (0xFF = desconhecido)
    )
    bs[510:512] = b"\x55\xAA"          # BootSignature

    regiao = bytes(bs) + bytes(10 * BYTES_POR_SETOR)
    soma = checksum_boot(regiao)
    setor_checksum = struct.pack("<I", soma) * (BYTES_POR_SETOR // 4)
    return regiao + setor_checksum      # 12 setores


def _boot_region_valida(regiao: bytes) -> bool:
    if len(regiao) != SETORES_BOOT_REGION * BYTES_POR_SETOR:
        return False
    if regiao[3:11] != b"EXFAT   " or regiao[510:512] != b"\x55\xAA":
        return False
    corpo = regiao[: 11 * BYTES_POR_SETOR]
    esperado = struct.pack("<I", checksum_boot(corpo)) * (BYTES_POR_SETOR // 4)
    return regiao[11 * BYTES_POR_SETOR:] == esperado


# ============================================================== classe Volume
class Volume:
    """Volume exFAT montado sobre um arquivo de imagem.

    Uso recomendado (monta e desmonta automaticamente):

        Volume.format("disco.img", tamanho=16 * 1024 * 1024)
        with Volume("disco.img") as vol:
            clusters, sem_fat = vol.alloc_clusters(3)
            vol.write_data(clusters, b"ola mundo")
    """

    # ------------------------------------------------------------ formatação
    @staticmethod
    def format(caminho: str, tamanho: int = 16 * 1024 * 1024,
               bytes_por_cluster: int = 4096) -> None:
        """Cria (ou recria) uma imagem formatada como exFAT."""
        if bytes_por_cluster < BYTES_POR_SETOR or \
                bytes_por_cluster & (bytes_por_cluster - 1):
            raise ValueError("bytes_por_cluster deve ser potência de 2 >= 512")
        if bytes_por_cluster > 32 * 1024 * 1024:
            raise ValueError("exFAT permite cluster de no máximo 32 MB")

        spc = bytes_por_cluster // BYTES_POR_SETOR
        spc_shift = spc.bit_length() - 1
        total_setores = tamanho // BYTES_POR_SETOR

        # O tamanho da FAT depende do nº de clusters e vice-versa:
        # estima pelo máximo e recalcula.
        max_clusters = (total_setores - FAT_OFFSET_SETORES) // spc
        fat_length = math.ceil((max_clusters + 2) * 4 / BYTES_POR_SETOR)
        heap_offset = FAT_OFFSET_SETORES + fat_length
        cluster_count = (total_setores - heap_offset) // spc
        if cluster_count < 4:
            raise ValueError("disco pequeno demais")

        # Bitmap: 1 bit por cluster, guardado no próprio heap a partir do cluster 2
        bitmap_bytes = math.ceil(cluster_count / 8)
        bitmap_clusters = math.ceil(bitmap_bytes / bytes_por_cluster)
        cadeia_bitmap = list(range(PRIMEIRO_CLUSTER, PRIMEIRO_CLUSTER + bitmap_clusters))
        root_cluster = cadeia_bitmap[-1] + 1

        campos = dict(volume_length=total_setores, fat_offset=FAT_OFFSET_SETORES,
                      fat_length=fat_length, heap_offset=heap_offset,
                      cluster_count=cluster_count, root_cluster=root_cluster,
                      serial=random.getrandbits(32), spc_shift=spc_shift)

        with open(caminho, "wb") as f:
            f.truncate(total_setores * BYTES_POR_SETOR)

            # Boot Region principal e backup
            regiao = _montar_boot_region(campos)
            f.seek(0)
            f.write(regiao)
            f.write(regiao)

            # FAT: entradas 0 e 1 são reservadas
            fat_base = FAT_OFFSET_SETORES * BYTES_POR_SETOR

            def set_fat(n, v):
                f.seek(fat_base + n * 4)
                f.write(struct.pack("<I", v))

            set_fat(0, 0xFFFFFFF8)          # media type
            set_fat(1, 0xFFFFFFFF)
            for cadeia in (cadeia_bitmap, [root_cluster]):
                for atual, prox in zip(cadeia, cadeia[1:] + [FAT_FIM]):
                    set_fat(atual, prox)

            # Bitmap: marca os clusters do próprio bitmap e da raiz como usados
            bitmap = bytearray(bitmap_clusters * bytes_por_cluster)
            for cl in cadeia_bitmap + [root_cluster]:
                i = cl - PRIMEIRO_CLUSTER
                bitmap[i // 8] |= 1 << (i % 8)
            heap_base = heap_offset * BYTES_POR_SETOR
            f.seek(heap_base + (cadeia_bitmap[0] - PRIMEIRO_CLUSTER) * bytes_por_cluster)
            f.write(bitmap)

            # Diretório raiz: primeira entrada aponta para o Allocation Bitmap
            entrada = bytearray(TAM_ENTRADA_DIR)
            entrada[0] = TIPO_ENTRADA_BITMAP
            struct.pack_into("<IQ", entrada, 20, cadeia_bitmap[0], bitmap_bytes)
            f.seek(heap_base + (root_cluster - PRIMEIRO_CLUSTER) * bytes_por_cluster)
            f.write(entrada)

    # -------------------------------------------------------- montagem
    def __init__(self, caminho: str):
        self.caminho = caminho
        self._f = open(caminho, "r+b")
        self._aberto = False
        self.recuperado_do_backup = False

        # CORREÇÃO: se qualquer etapa da montagem falhar, o arquivo é fechado
        # e o flag VolumeDirty NÃO é ligado (ele só é ligado no final).
        try:
            # 1) Lê e valida a Boot Region; se estiver corrompida, usa o backup
            tam_regiao = SETORES_BOOT_REGION * BYTES_POR_SETOR
            self._f.seek(0)
            principal = self._f.read(tam_regiao)
            if not _boot_region_valida(principal):
                backup = self._f.read(tam_regiao)
                if not _boot_region_valida(backup):
                    raise ErroVolume("Boot Region principal e backup corrompidas")
                self._f.seek(0)
                self._f.write(backup)                 # restaura a principal
                principal = backup
                self.recuperado_do_backup = True

            (_, self.volume_length, self.fat_offset, self.fat_length,
             self.heap_offset, self.cluster_count, self.root_cluster,
             self.serial, _, flags, _, spc_shift, _, _, _) = \
                struct.unpack_from(FORMATO_CAMPOS_BOOT, principal, 64)

            self.cluster_size = BYTES_POR_SETOR << spc_shift
            self._fat_base = self.fat_offset * BYTES_POR_SETOR
            self._heap_base = self.heap_offset * BYTES_POR_SETOR

            # 2) Carrega o Allocation Bitmap (localizado pela entrada 0x81 da raiz)
            self._carregar_bitmap()

            # 3) VolumeDirty: se já estava ligado, o volume não foi desmontado direito
            self.estava_sujo = bool(flags & FLAG_VOLUME_DIRTY)
            self._gravar_flags(flags | FLAG_VOLUME_DIRTY)
        except Exception:
            self._f.close()
            raise
        self._aberto = True

    def close(self) -> None:
        """Desmonta: grava o bitmap, atualiza % de uso e limpa VolumeDirty."""
        if not self._aberto:
            return
        self._flush_bitmap()
        uso = round(100 * (self.cluster_count - self.free_count()) / self.cluster_count)
        self._f.seek(OFF_PERCENT_IN_USE)
        self._f.write(bytes([uso]))
        self._f.seek(OFF_VOLUME_FLAGS)
        flags = struct.unpack("<H", self._f.read(2))[0]
        self._gravar_flags(flags & ~FLAG_VOLUME_DIRTY)
        self._f.flush()
        os.fsync(self._f.fileno())
        self._f.close()
        self._aberto = False

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()

    def _gravar_flags(self, flags: int) -> None:
        self._f.seek(OFF_VOLUME_FLAGS)
        self._f.write(struct.pack("<H", flags))
        self._f.flush()

    # -------------------------------------------------------- clusters
    def _checar_cluster(self, n: int) -> None:
        if not PRIMEIRO_CLUSTER <= n < PRIMEIRO_CLUSTER + self.cluster_count:
            raise ErroVolume(f"cluster {n} fora do volume")

    def read_cluster(self, n: int) -> bytes:
        """Lê um cluster inteiro."""
        self._checar_cluster(n)
        self._f.seek(self._heap_base + (n - PRIMEIRO_CLUSTER) * self.cluster_size)
        return self._f.read(self.cluster_size)

    def write_cluster(self, n: int, dados: bytes) -> None:
        """Grava um cluster (completa com zeros se 'dados' for menor)."""
        self._checar_cluster(n)
        if len(dados) > self.cluster_size:
            raise ErroVolume("dados maiores que um cluster")
        self._f.seek(self._heap_base + (n - PRIMEIRO_CLUSTER) * self.cluster_size)
        self._f.write(dados.ljust(self.cluster_size, b"\x00"))

    def clusters_needed(self, tamanho: int) -> int:
        """Quantos clusters são necessários para 'tamanho' bytes."""
        return math.ceil(tamanho / self.cluster_size)

    # -------------------------------------------------------- FAT
    def _checar_indice_fat(self, n: int) -> None:
        # CORREÇÃO: a FAT tem cluster_count + 2 entradas (0 e 1 são reservadas)
        if not 0 <= n < self.cluster_count + PRIMEIRO_CLUSTER:
            raise ErroVolume(f"índice {n} fora da FAT")

    def read_fat(self, n: int) -> int:
        self._checar_indice_fat(n)
        self._f.seek(self._fat_base + n * 4)
        return struct.unpack("<I", self._f.read(4))[0]

    def write_fat(self, n: int, valor: int) -> None:
        self._checar_indice_fat(n)
        self._f.seek(self._fat_base + n * 4)
        self._f.write(struct.pack("<I", valor))

    def _encadear(self, clusters: list) -> None:
        """Grava a cadeia na FAT: cada cluster aponta para o próximo."""
        for atual, prox in zip(clusters, clusters[1:] + [FAT_FIM]):
            self.write_fat(atual, prox)

    # -------------------------------------------------------- bitmap
    def _carregar_bitmap(self) -> None:
        for cl in self.get_chain(self.root_cluster):
            dados = self.read_cluster(cl)
            for off in range(0, len(dados), TAM_ENTRADA_DIR):
                if dados[off] == TIPO_ENTRADA_BITMAP:
                    primeiro, tamanho = struct.unpack_from("<IQ", dados, off + 20)
                    self._cadeia_bitmap = self.get_chain(primeiro)
                    self._bitmap = bytearray(self.read_data(self._cadeia_bitmap, tamanho))
                    return
        raise ErroVolume("entrada do Allocation Bitmap não encontrada na raiz")

    def _flush_bitmap(self) -> None:
        self.write_data(self._cadeia_bitmap, bytes(self._bitmap))

    def is_free(self, n: int) -> bool:
        i = n - PRIMEIRO_CLUSTER
        return not (self._bitmap[i // 8] >> (i % 8)) & 1

    def _marcar(self, n: int, usado: bool) -> None:
        i = n - PRIMEIRO_CLUSTER
        if usado:
            self._bitmap[i // 8] |= 1 << (i % 8)
        else:
            self._bitmap[i // 8] &= ~(1 << (i % 8))

    def free_count(self) -> int:
        """Número de clusters livres."""
        usados = sum(bin(b).count("1") for b in self._bitmap)
        return self.cluster_count - usados

    # -------------------------------------------------------- alocação
    def _procurar_contiguos(self, qtd: int):
        """Primeiro trecho com 'qtd' clusters livres seguidos (first-fit)."""
        inicio, seguidos = None, 0
        for n in range(PRIMEIRO_CLUSTER, PRIMEIRO_CLUSTER + self.cluster_count):
            if self.is_free(n):
                if seguidos == 0:
                    inicio = n
                seguidos += 1
                if seguidos == qtd:
                    return inicio
            else:
                seguidos = 0
        return None

    def alloc_clusters(self, qtd: int):
        """Aloca 'qtd' clusters.

        Retorna (lista_de_clusters, no_fat_chain):
          * no_fat_chain=True  -> clusters contíguos; a FAT NÃO é usada
            (é a otimização NoFatChain do exFAT). A Parte 2 deve guardar
            esse flag na entrada Stream Extension do arquivo.
          * no_fat_chain=False -> arquivo fragmentado; a cadeia está na FAT.
        """
        if qtd <= 0:
            return [], False
        if qtd > self.free_count():
            raise EspacoInsuficiente(f"pedidos {qtd} clusters, livres {self.free_count()}")

        inicio = self._procurar_contiguos(qtd)
        if inicio is not None:
            clusters = list(range(inicio, inicio + qtd))
            sem_fat = True
        else:
            livres = (n for n in range(PRIMEIRO_CLUSTER, PRIMEIRO_CLUSTER + self.cluster_count)
                      if self.is_free(n))
            clusters = [next(livres) for _ in range(qtd)]
            self._encadear(clusters)
            sem_fat = False

        for n in clusters:
            self._marcar(n, True)
        self._flush_bitmap()
        return clusters, sem_fat

    def extend_chain(self, clusters: list, no_fat_chain: bool, extra: int):
        """Aumenta uma cadeia em 'extra' clusters (usado no append/overwrite).

        Se a cadeia é contígua e os clusters seguintes estão livres, ela
        continua contígua. Se não, é convertida para cadeia na FAT —
        exatamente como o exFAT faz. Retorna (nova_lista, no_fat_chain).
        """
        if extra <= 0:
            return clusters, no_fat_chain
        if not clusters:
            return self.alloc_clusters(extra)

        ultimo = clusters[-1]
        if no_fat_chain:
            seguintes = range(ultimo + 1, ultimo + 1 + extra)
            if seguintes[-1] < PRIMEIRO_CLUSTER + self.cluster_count and \
                    all(self.is_free(n) for n in seguintes):
                for n in seguintes:
                    self._marcar(n, True)
                self._flush_bitmap()
                return clusters + list(seguintes), True

        novos, _ = self.alloc_clusters(extra)
        cadeia = clusters + novos
        self._encadear(cadeia)
        return cadeia, False

    def free_clusters(self, clusters: list) -> None:
        """Libera clusters (marca livres no bitmap e zera a FAT)."""
        for n in clusters:
            self._checar_cluster(n)
            self._marcar(n, False)
            self.write_fat(n, FAT_LIVRE)
        self._flush_bitmap()

    def shrink_chain(self, clusters: list, no_fat_chain: bool, manter: int) -> list:
        """Mantém só os 'manter' primeiros clusters e libera o resto."""
        mantidos, sobra = clusters[:manter], clusters[manter:]
        if sobra:
            self.free_clusters(sobra)
            if mantidos and not no_fat_chain:
                self.write_fat(mantidos[-1], FAT_FIM)
        return mantidos

    def get_chain(self, primeiro: int, tamanho: int = None,
                  no_fat_chain: bool = False) -> list:
        """Reconstrói a lista de clusters de um arquivo/diretório.

        * no_fat_chain=True: basta o primeiro cluster e o tamanho.
        * no_fat_chain=False: segue a FAT até o End Of Chain.
        """
        if primeiro == 0:
            return []
        if no_fat_chain:
            if tamanho is None:
                raise ValueError("NoFatChain exige o tamanho")
            return list(range(primeiro, primeiro + self.clusters_needed(tamanho)))

        cadeia, atual = [], primeiro
        while atual != FAT_FIM:
            self._checar_cluster(atual)
            cadeia.append(atual)
            if len(cadeia) > self.cluster_count:
                raise ErroVolume("cadeia da FAT corrompida (loop)")
            atual = self.read_fat(atual)
            if atual in (FAT_LIVRE, FAT_RUIM):
                raise ErroVolume(f"cadeia quebrada no cluster {cadeia[-1]}")
        return cadeia

    # -------------------------------------------------------- dados
    def write_data(self, clusters: list, dados: bytes) -> None:
        """Grava 'dados' espalhados pelos clusters da lista."""
        if len(dados) > len(clusters) * self.cluster_size:
            raise ErroVolume("dados não cabem nos clusters informados")
        cs = self.cluster_size
        for i, n in enumerate(clusters):
            self.write_cluster(n, dados[i * cs:(i + 1) * cs])

    def read_data(self, clusters: list, tamanho: int) -> bytes:
        """Lê 'tamanho' bytes a partir da lista de clusters."""
        dados = b"".join(self.read_cluster(n) for n in clusters)
        return dados[:tamanho]

    # -------------------------------------------------------- informação
    def info(self) -> dict:
        return {
            "arquivo de imagem": self.caminho,
            "tamanho do volume (bytes)": self.volume_length * BYTES_POR_SETOR,
            "tamanho do cluster (bytes)": self.cluster_size,
            "clusters no heap": self.cluster_count,
            "clusters livres": self.free_count(),
            "FAT (setor inicial / setores)": (self.fat_offset, self.fat_length),
            "cluster heap (setor inicial)": self.heap_offset,
            "cluster da raiz": self.root_cluster,
            "clusters do bitmap": self._cadeia_bitmap,
            "número de série": f"{self.serial:08X}",
            "estava sujo ao montar": self.estava_sujo,
            "recuperado do backup": self.recuperado_do_backup,
        }


# ---------------------------------------------------------------- demonstração
if __name__ == "__main__":
    img = "demo.img"
    Volume.format(img, tamanho=8 * 1024 * 1024)
    with Volume(img) as vol:
        for k, v in vol.info().items():
            print(f"{k:32} {v}")
        texto = b"Ola, exFAT! " * 1000
        clusters, sem_fat = vol.alloc_clusters(vol.clusters_needed(len(texto)))
        vol.write_data(clusters, texto)
        print(f"\nGravados {len(texto)} bytes em {clusters} (NoFatChain={sem_fat})")
        print("Leitura confere:", vol.read_data(clusters, len(texto)) == texto)