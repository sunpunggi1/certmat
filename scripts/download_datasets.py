"""CertMat 공개 데이터셋 일괄 다운로드 및 스키마 점검 스크립트."""

import gzip
import json
import sys
from pathlib import Path

import pandas as pd

ROOT_DIR = Path(__file__).resolve().parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from certmat.datasets import DATA_DIR, download_all_datasets


def main() -> None:
    manifest = download_all_datasets(DATA_DIR)
    print("\n=== 다운로드 완료 요약 ===")
    for k, v in manifest.items():
        print(f"- {k}: {v['file']} ({v['bytes']/1e6:.2f} MB) sha256={v['sha256'][:16]}...")

    # 스키마 신속 점검
    print("\n=== GNoME PBE 스키마 ===")
    df_pbe = pd.read_csv(DATA_DIR / "gnome_stable_materials_summary.csv", nrows=5)
    print("Columns:", list(df_pbe.columns))
    print(df_pbe.head(2).to_string())

    print("\n=== GNoME r2SCAN 스키마 ===")
    df_r2 = pd.read_csv(DATA_DIR / "gnome_stable_materials_r2scan.csv", nrows=5)
    print("Columns:", list(df_r2.columns))
    print(df_r2.head(2).to_string())

    print("\n=== WBM Summary 스키마 ===")
    df_wbm = pd.read_csv(DATA_DIR / "wbm_summary.csv.gz", nrows=5)
    print("Columns:", list(df_wbm.columns))
    print(df_wbm.head(2).to_string())

    print("\n=== JARVIS-DFT 3D 스키마 ===")
    with open(DATA_DIR / "jdft_3d.json", "r", encoding="utf-8") as f:
        jdata = json.load(f)
    print(f"Total JARVIS records: {len(jdata)}")
    print("Sample keys:", sorted(list(jdata[0].keys())))
    has_el = sum(
        1 for r in jdata
        if isinstance(r.get("elastic_tensor"), list) and len(r["elastic_tensor"]) == 6
    )
    print(f"Records with 6x6 elastic_tensor: {has_el}")


if __name__ == "__main__":
    main()
