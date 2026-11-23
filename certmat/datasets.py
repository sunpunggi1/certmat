"""
CertMat 공개 재료 데이터베이스 다운로드 및 무결성(SHA-256) 관리 모듈.

대상 데이터셋:
1. Google DeepMind GNoME:
   - stable_materials_summary.csv (PBE 기준 안정 후보 전수)
   - stable_materials_r2scan.csv (고정밀 r2SCAN 교차검증 데이터)
2. NIST JARVIS-DFT 3D (jdft_3d.json):
   - 형성에너지(formation_energy_peratom), ehull, 6x6 탄성 텐서(elastic_tensor), 공간군(spg_number)
3. Matbench Discovery WBM (wbm-summary.csv.gz):
   - 대규모 치환 구조 WBM 데이터셋의 형성에너지 및 Convex Hull 거리
"""

from __future__ import annotations

import gzip
import hashlib
import json
import os
import zipfile
from pathlib import Path
from typing import Dict, Any, Optional

import requests

DATA_DIR = Path(__file__).resolve().parent.parent / "data"

# GNoME 공식 Google Cloud Storage 공개 HTTPS 경로
GNOME_PBE_URL = (
    "https://storage.googleapis.com/gdm_materials_discovery/"
    "gnome_data/stable_materials_summary.csv"
)
GNOME_R2SCAN_URL = (
    "https://storage.googleapis.com/gdm_materials_discovery/"
    "gnome_data/stable_materials_r2scan.csv"
)

# NIST JARVIS-DFT 3D Figshare 레코드 (DOI: 10.6084/m9.figshare.6815699)
JARVIS_FIGSHARE_API = "https://api.figshare.com/v2/articles/6815699"
JARVIS_FALLBACK_URL = "https://figshare.com/ndownloader/files/38521619"

# Matbench Discovery Figshare 레코드 (Article 22715158)
WBM_FIGSHARE_API = "https://api.figshare.com/v2/articles/22715158"

# 재현성 검증용 소스코드 고정(hard-pinned) 원본 데이터셋 SHA-256 해시
# (TOFU 자동 덮어쓰기 방지: 다운로드 결과가 고정 해시와 다르면 즉시 예외 발생)
PINNED_DATASET_SHA256: Dict[str, str] = {
    "gnome_pbe": "c37bffb9dd6c51d38d259a2d340ecf796194729f656d474828512390db1ff0c9",
    "gnome_r2scan": "6a811395b065f43ae7911597405eec0ecfa88251e918f4c0ba8e4e99a75656fd",
    "jarvis_dft_3d": "9dacb55ac8371c7c2bf0332933b55c98e9cca6201e92eb9d6fcd03aab0975907",
    "matbench_wbm": "68441da399d68f0da3183c692f51b115957e8da1e2ed809fd03e8859302992a2",
}


def verify_pinned_sha256(key: str, path: Path) -> str:
    """소스코드 고정 SHA-256 해시와 파일 해시가 일치하는지 검증하고 불일치 시 즉시 실패한다."""
    actual = sha256_file(path)
    expected = PINNED_DATASET_SHA256.get(key)
    if expected is not None and actual != expected:
        raise RuntimeError(
            f"데이터셋 '{key}'({path.name}) SHA-256 불일치: "
            f"expected={expected}, actual={actual} (소스 고정 해시 위반)"
        )
    return actual


def sha256_file(path: Path, chunk_size: int = 1 << 20) -> str:
    """파일의 SHA-256 해시를 계산한다."""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            chunk = f.read(chunk_size)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()


def download_file(
    url: str,
    dest: Path,
    timeout: int = 120,
    expected_sha256: Optional[str] = None,
) -> Path:
    """스트리밍 방식으로 대용량 파일을 다운로드하며, 캐시 파일은 SHA-256 일치 시에만 재사용한다."""
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists() and dest.stat().st_size > 1024:
        if expected_sha256 is None or sha256_file(dest) == expected_sha256:
            print(f"[캐시 사용] {dest.name} ({dest.stat().st_size / 1e6:.2f} MB)")
            return dest
        print(f"[경고] 캐시 파일 {dest.name} 의 SHA-256 불일치 — 재다운로드합니다.")
    print(f"[다운로드 시작] {url} -> {dest.name}")
    headers = {"User-Agent": "CertMat-Research/1.0"}
    with requests.get(url, stream=True, timeout=timeout, headers=headers) as r:
        r.raise_for_status()
        tmp = dest.with_suffix(dest.suffix + ".part")
        total = 0
        with open(tmp, "wb") as f:
            for chunk in r.iter_content(chunk_size=1 << 20):
                if chunk:
                    f.write(chunk)
                    total += len(chunk)
        tmp.replace(dest)
    print(f"[다운로드 완료] {dest.name} ({total / 1e6:.2f} MB)")
    return dest


def resolve_figshare_file(api_url: str, predicate) -> Optional[Dict[str, Any]]:
    """Figshare API v2에서 조건에 맞는 최신 파일 메타데이터를 파일 ID(숫자) 내림차순으로 조회한다."""
    r = requests.get(api_url, timeout=30, headers={"User-Agent": "CertMat-Research/1.0"})
    r.raise_for_status()
    info = r.json()
    matches = [f for f in info.get("files", []) if predicate(f["name"])]
    if not matches:
        return None
    matches.sort(key=lambda x: (int(x.get("id", 0)), x["name"]), reverse=True)
    return matches[0]


def download_all_datasets(data_dir: Path = DATA_DIR) -> Dict[str, Any]:
    """3대 공개 재료 데이터셋을 모두 내려받고 SHA-256 매니페스트를 저장한다."""
    data_dir.mkdir(parents=True, exist_ok=True)
    manifest_path = data_dir / "dataset_manifest.json"
    prev_manifest: Dict[str, Any] = {}
    if manifest_path.exists():
        try:
            with open(manifest_path, "r", encoding="utf-8") as f:
                prev_manifest = json.load(f)
        except Exception:
            prev_manifest = {}

    manifest: Dict[str, Any] = {}

    # 1. DeepMind GNoME (PBE + r2SCAN)
    gnome_pbe = download_file(
        GNOME_PBE_URL,
        data_dir / "gnome_stable_materials_summary.csv",
        expected_sha256=PINNED_DATASET_SHA256["gnome_pbe"],
    )
    gnome_r2 = download_file(
        GNOME_R2SCAN_URL,
        data_dir / "gnome_stable_materials_r2scan.csv",
        expected_sha256=PINNED_DATASET_SHA256["gnome_r2scan"],
    )
    manifest["gnome_pbe"] = {
        "file": gnome_pbe.name,
        "url": GNOME_PBE_URL,
        "bytes": gnome_pbe.stat().st_size,
        "sha256": verify_pinned_sha256("gnome_pbe", gnome_pbe),
    }
    manifest["gnome_r2scan"] = {
        "file": gnome_r2.name,
        "url": GNOME_R2SCAN_URL,
        "bytes": gnome_r2.stat().st_size,
        "sha256": verify_pinned_sha256("gnome_r2scan", gnome_r2),
    }

    # 2. NIST JARVIS-DFT 3D
    jarvis_json = data_dir / "jdft_3d.json"
    jarvis_zip = data_dir / "jdft_3d.json.zip"
    prev_j = prev_manifest.get("jarvis_dft_3d", {})
    cached_j_ok = (
        jarvis_json.exists()
        and jarvis_json.stat().st_size >= 1024
        and sha256_file(jarvis_json) == PINNED_DATASET_SHA256["jarvis_dft_3d"]
    )
    if not cached_j_ok:
        meta = None
        try:
            meta = resolve_figshare_file(
                JARVIS_FIGSHARE_API,
                lambda n: "jdft_3d" in n.lower() and n.lower().endswith(".zip"),
            )
        except Exception as exc:
            print(f"[경고] JARVIS Figshare API 조회 실패({exc}), 기본 URL 사용")
        j_url = meta["download_url"] if meta else JARVIS_FALLBACK_URL
        download_file(j_url, jarvis_zip, timeout=300)
        print("[압축 해제] JARVIS-DFT 3D ZIP -> jdft_3d.json")
        with zipfile.ZipFile(jarvis_zip, "r") as zf:
            json_names = [n for n in zf.namelist() if n.endswith(".json")]
            if not json_names:
                raise RuntimeError(f"ZIP 내 JSON 없음: {zf.namelist()}")
            with zf.open(json_names[0]) as src, open(jarvis_json, "wb") as dst:
                while True:
                    buf = src.read(1 << 20)
                    if not buf:
                        break
                    dst.write(buf)
        j_source_url = j_url
    else:
        j_source_url = prev_j.get("url", JARVIS_FALLBACK_URL)
    manifest["jarvis_dft_3d"] = {
        "file": jarvis_json.name,
        "url": j_source_url,
        "bytes": jarvis_json.stat().st_size,
        "sha256": verify_pinned_sha256("jarvis_dft_3d", jarvis_json),
    }

    # 3. Matbench Discovery WBM summary
    wbm_gz = data_dir / "wbm_summary.csv.gz"
    prev_w = prev_manifest.get("matbench_wbm", {})
    cached_w_ok = (
        wbm_gz.exists()
        and wbm_gz.stat().st_size >= 1024
        and sha256_file(wbm_gz) == PINNED_DATASET_SHA256["matbench_wbm"]
    )
    if not cached_w_ok:
        meta = resolve_figshare_file(
            WBM_FIGSHARE_API,
            lambda n: "wbm" in n.lower() and "summary" in n.lower() and n.lower().endswith(".csv.gz"),
        )
        if meta is None:
            raise RuntimeError("Matbench Discovery Figshare에서 wbm-summary.csv.gz를 찾지 못했습니다.")
        wbm_url = meta["download_url"]
        download_file(wbm_url, wbm_gz, timeout=300)
    else:
        wbm_url = prev_w.get("url", WBM_FIGSHARE_API)
    manifest["matbench_wbm"] = {
        "file": wbm_gz.name,
        "url": wbm_url,
        "bytes": wbm_gz.stat().st_size,
        "sha256": verify_pinned_sha256("matbench_wbm", wbm_gz),
    }

    with open(manifest_path, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, ensure_ascii=False)
    print(f"[매니페스트 저장 완료] {manifest_path}")
    return manifest


if __name__ == "__main__":
    download_all_datasets()
