"""
NIST JARVIS-DFT 3D (`jdft_3d-9-24-2025.json`) 공개 `ehull` 컬럼의
이중 나눗셈(double-division by N_fu) 단위 결함을 독립적으로 최소 재현하는 스크립트.

사용법:
    .venv\\Scripts\\python.exe scripts/repro_jarvis_ehull_bug.py
"""

from __future__ import annotations

import json
import math
import statistics
import sys
from pathlib import Path
from typing import Dict, List

import numpy as np

ROOT_DIR = Path(__file__).resolve().parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from certmat.phase_audit import parse_formula_counts


def main() -> None:
    """`data/jdft_3d.json`을 직접 읽어 공개 `ehull` 이중 나눗셈 결함과 음성대조군을 재현한다."""
    jdft_path = ROOT_DIR / "data" / "jdft_3d.json"
    with open(jdft_path, "r", encoding="utf-8") as f:
        records = json.load(f)

    # 1. 단원자 화학식(예: 'Fe', 'Si')에서 원소별 최저 optb88vdw_total_energy 수집
    elem_o88: Dict[str, float] = {}
    all_ehull: List[float] = []
    elem_ehull: List[float] = []

    for rec in records:
        eh = rec.get("ehull")
        o88 = rec.get("optb88vdw_total_energy")
        if not (isinstance(eh, (int, float)) and math.isfinite(eh)):
            continue
        all_ehull.append(float(eh))
        try:
            cnt = parse_formula_counts(rec["formula"])
        except Exception:
            continue
        if len(cnt) == 1:
            elem_ehull.append(float(eh))
            if (
                float(next(iter(cnt.values()))) == 1.0
                and isinstance(o88, (int, float))
                and math.isfinite(o88)
            ):
                el = next(iter(cnt))
                if el not in elem_o88 or float(o88) < elem_o88[el]:
                    elem_o88[el] = float(o88)

    # 2. 다원계(n_fu > 1)에서 이중 나눗셈 모델과 두 음성대조군의 절대 잔차 비교
    rng = np.random.default_rng(2026)
    elem_vals = list(elem_o88.values())
    rand_elem_o88 = {el: float(rng.choice(elem_vals)) for el in elem_o88}

    res_div: List[float] = []
    res_nodiv: List[float] = []
    res_rand: List[float] = []
    by_jid: Dict[str, Dict[str, float]] = {}

    for rec in records:
        eh = rec.get("ehull")
        o88 = rec.get("optb88vdw_total_energy")
        if not (
            isinstance(eh, (int, float))
            and isinstance(o88, (int, float))
            and math.isfinite(eh)
            and math.isfinite(o88)
        ):
            continue
        try:
            cnt = parse_formula_counts(rec["formula"])
        except Exception:
            continue
        n_fu = float(sum(cnt.values()))
        if len(cnt) <= 1 or n_fu <= 1.0 or not all(el in elem_o88 for el in cnt):
            continue
        e_elem = sum((float(c) / n_fu) * elem_o88[el] for el, c in cnt.items())
        e_rand = sum((float(c) / n_fu) * rand_elem_o88[el] for el, c in cnt.items())
        pred_div = (float(o88) / n_fu) - e_elem
        pred_nodiv = float(o88) - e_elem
        pred_rand = (float(o88) / n_fu) - e_rand

        res_div.append(abs(pred_div - float(eh)))
        res_nodiv.append(abs(pred_nodiv - float(eh)))
        res_rand.append(abs(pred_rand - float(eh)))
        by_jid[rec["jid"]] = {
            "formula": rec["formula"],
            "n_fu": n_fu,
            "o88": float(o88),
            "fe": float(rec.get("formation_energy_peratom", float("nan"))),
            "ehull": float(eh),
            "pred_div": pred_div,
            "abs_diff": abs(pred_div - float(eh)),
        }

    gt_05 = sum(1 for v in all_ehull if v > 0.5)
    gt_10 = sum(1 for v in all_ehull if v > 1.0)
    print(f"Total finite ehull entries : {len(all_ehull):,}")
    print(f"Overall median ehull       : {statistics.median(all_ehull):.4f} eV/atom")
    print(f"ehull > 0.5 eV/atom        : {gt_05:,} ({100.0 * gt_05 / len(all_ehull):.2f}%)")
    print(f"ehull > 1.0 eV/atom        : {gt_10:,} ({100.0 * gt_10 / len(all_ehull):.2f}%)")
    print(f"Single-element (N_fu=1)    : n={len(elem_ehull):,}, median={statistics.median(elem_ehull):.4f} eV/atom")
    print(f"\nMultinary forensic check (n={len(res_div):,}):")
    for name, arr in (
        ("Double-division model (E_optB88 / N_fu - E_elem)", res_div),
        ("Negative control 1 (no 1/N_fu division)", res_nodiv),
        ("Negative control 2 (permuted elem. refs)", res_rand),
    ):
        a = np.asarray(arr, dtype=np.float64)
        print(
            f"  - {name:<50s}: median={np.median(a):.5f} eV | "
            f"<0.01 eV={100.0 * (a < 0.01).mean():.2f}% | "
            f"<0.05 eV={100.0 * (a < 0.05).mean():.2f}%"
        )

    print("\nRepresentative stable ground-state examples:")
    for jid in ("JVASP-106708", "JVASP-15157", "JVASP-13318", "JVASP-152492", "JVASP-109512"):
        row = by_jid[jid]
        print(
            f"  {jid:<12s} {row['formula']:<12s} N_fu={int(row['n_fu']):<2d} "
            f"fe={row['fe']:+.5f} o88={row['o88']:+.5f} "
            f"published_ehull={row['ehull']:.4f} pred_div={row['pred_div']:.4f} diff={row['abs_diff']:.5f}"
        )


if __name__ == "__main__":
    main()
