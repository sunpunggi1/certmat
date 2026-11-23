"""
CertMat 심층 보완 분석 스크립트 (적대적 교차심사 전수 대응):
1. JARVIS 탄성 텐서 심층 분해 (전수 정확 유리수 LDL^T — 부동소수점 단축 없음):
   - Born Non-PD(11,481건)의 심각도 구간 분포 (경미 0..-10, 중등 -10..-50, 심각 -50..-1000, 극단 <-1000 GPa)
   - Born-PD(22,842건) 내부의 축치환 대칭성 위반 및 순수 유리수 SO(3)-불변 Mandel/Kelvin Weyl 강건성 분포
2. GNoME PBE-r2SCAN 117,043건 5-Fold Out-of-Sample 검증:
   - (A) 외부 `Decomposition Energy Per Atom` 프록시 점수 기준: 무작위 5-Fold + 화학계 그룹화(Chemical-System GroupKFold)
         5-Fold 비교, 95% 부트스트랩 ΔAUC 신뢰구간, 보정 곡선, 실측 잔차 커버리지(|η_i| ≤ w_i) 측정
   - (B) 실제 정확 Charnes-Cooper LP 이질적 증명서 기준: 화학계 그룹화 5-Fold 교차검증(훈련 4폴드에서
         화학군별 잔차 MAE/p75 보정 → 평가 폴드의 동일 화학계에 실제 Charnes-Cooper 정확 LP 실행)으로
         실제 r2SCAN 전복 예측력(ROC-AUC, PPV/NPV, 상대위험도, ΔAUC 95% CI)을 직접 검증
"""

from __future__ import annotations

import argparse
import csv
import ctypes
import json
import math
import os
import sys
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import numpy as np
from scipy.optimize import minimize

ROOT_DIR = Path(__file__).resolve().parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from certmat.datasets import DATA_DIR
from certmat.elastic_audit import (
    MANDEL_WEIGHTS,
    compute_voigt_symmetry_violations,
    exact_ldlt_or_counterexample,
    weighted_shift_matrix_exact,
)
from certmat.exact_lp import to_fraction
from certmat.phase_audit import (
    PhaseDiagramIndex,
    PhaseEntry,
    audit_single_phase,
    formula_to_atom_fractions,
)
from certmat.uncertainty import (
    HETERO_CHEM_PROFILE,
    HETERO_CHEM_ZERO_ELEM_PROFILE,
    classify_chemistry,
    decompose_reference_and_residual_errors,
)

RESULTS_DIR = ROOT_DIR / "results"


def _roc_auc(labels: np.ndarray, scores: np.ndarray) -> float:
    labels = np.asarray(labels, dtype=np.int64)
    scores = np.asarray(scores, dtype=np.float64)
    pos = labels == 1
    neg = labels == 0
    n_pos, n_neg = int(pos.sum()), int(neg.sum())
    if n_pos == 0 or n_neg == 0:
        return float("nan")
    order = np.argsort(scores, kind="mergesort")
    ranks = np.empty(len(scores), dtype=np.float64)
    s_sorted = scores[order]
    i, n = 0, len(scores)
    while i < n:
        j = i + 1
        while j < n and s_sorted[j] == s_sorted[i]:
            j += 1
        ranks[order[i:j]] = 0.5 * (i + 1 + j)
        i = j
    u = ranks[pos].sum() - n_pos * (n_pos + 1) / 2.0
    return float(u / (n_pos * n_neg))


def _paired_bootstrap_delta_auc(
    labels: np.ndarray,
    scores_a: np.ndarray,
    scores_b: np.ndarray,
    groups: Optional[List[Tuple[str, ...]]] = None,
    n_boot: int = 1000,
    seed: int = 2026,
) -> Dict[str, float]:
    """동일 부트스트랩 표본에서 ΔAUC = AUC(a) - AUC(b) 의 점추정과 95% 신뢰구간을 계산한다.
    `groups` 가 주어지면 화학계(cluster) 단위로 복원추출하는 클러스터 부트스트랩을 수행한다.
    """
    base_a = _roc_auc(labels, scores_a)
    base_b = _roc_auc(labels, scores_b)
    rng = np.random.default_rng(seed)
    deltas = []
    if groups is not None:
        # 화학계 클러스터 단위 복원추출 (동일 화학계 내 상관 반영)
        by_grp: Dict[Tuple[str, ...], List[int]] = {}
        for idx, g in enumerate(groups):
            by_grp.setdefault(g, []).append(idx)
        clusters = [np.asarray(v, dtype=np.int64) for v in by_grp.values()]
        n_c = len(clusters)
        for _ in range(n_boot):
            chosen = rng.integers(0, n_c, size=n_c)
            idx = np.concatenate([clusters[c] for c in chosen])
            aa = _roc_auc(labels[idx], scores_a[idx])
            bb = _roc_auc(labels[idx], scores_b[idx])
            if math.isfinite(aa) and math.isfinite(bb):
                deltas.append(aa - bb)
    else:
        n = len(labels)
        for _ in range(n_boot):
            idx = rng.integers(0, n, size=n)
            aa = _roc_auc(labels[idx], scores_a[idx])
            bb = _roc_auc(labels[idx], scores_b[idx])
            if math.isfinite(aa) and math.isfinite(bb):
                deltas.append(aa - bb)
    arr = np.asarray(deltas, dtype=np.float64)
    return {
        "auc_a": round(base_a, 4),
        "auc_b": round(base_b, 4),
        "delta_auc": round(base_a - base_b, 4),
        "delta_ci95_low": round(float(np.percentile(arr, 2.5)), 4) if len(arr) else float("nan"),
        "delta_ci95_high": round(float(np.percentile(arr, 97.5)), 4) if len(arr) else float("nan"),
        "n_boot": n_boot,
        "bootstrap_unit": "chemical_system_cluster" if groups is not None else "iid_row",
    }


def _fit_logistic_margin_onehot(
    X_tr: np.ndarray, y_tr: np.ndarray, X_val: np.ndarray, l2: float = 1e-3
) -> np.ndarray:
    """외부 ML 라이브러리 없이 L2 정규화 로지스틱 회귀(마진 + 화학군 원핫 베이스라인)를 학습해 검증 로짓을 반환한다."""
    n, d = X_tr.shape
    w0 = np.zeros(d, dtype=np.float64)

    def _loss_grad(w: np.ndarray) -> Tuple[float, np.ndarray]:
        z = np.clip(X_tr @ w, -30.0, 30.0)
        p = 1.0 / (1.0 + np.exp(-z))
        # 수치 안정 이진 교차엔트로피
        loss = float(np.mean(np.logaddexp(0.0, z) - y_tr * z)) + 0.5 * l2 * float(np.dot(w[1:], w[1:]))
        grad = (X_tr.T @ (p - y_tr)) / n
        grad[1:] += l2 * w[1:]
        return loss, grad

    res = minimize(_loss_grad, w0, jac=True, method="L-BFGS-B", options={"maxiter": 200})
    return X_val @ res.x


def _safe_rr(frg_pos: int, frg_n: int, rob_pos: int, rob_n: int) -> Optional[float]:
    if frg_n == 0 or rob_n == 0 or rob_pos == 0:
        return None
    return round((frg_pos / frg_n) / (rob_pos / rob_n), 3)


def _group_kfold_indices(groups: List[Tuple[str, ...]], n_splits: int = 5, seed: int = 2026) -> List[np.ndarray]:
    """화학계(원소 집합) 단위로 결정론적 균형 GroupKFold 분할을 생성한다 (훈련·평가 간 화학계 중복 0건)."""
    by_grp: Dict[Tuple[str, ...], List[int]] = {}
    for idx, g in enumerate(groups):
        by_grp.setdefault(g, []).append(idx)
    rng = np.random.default_rng(seed)
    keys = list(by_grp.keys())
    rng.shuffle(keys)
    # 큰 그룹부터 가장 작은 폴드에 탐욕 배정해 폴드 크기 균형화
    keys.sort(key=lambda k: len(by_grp[k]), reverse=True)
    fold_lists: List[List[int]] = [[] for _ in range(n_splits)]
    for k in keys:
        smallest = min(range(n_splits), key=lambda f: len(fold_lists[f]))
        fold_lists[smallest].extend(by_grp[k])
    return [np.asarray(sorted(fl), dtype=np.int64) for fl in fold_lists]


def analyze_jarvis_elastic_deep() -> Dict[str, Any]:
    """전수 정확 유리수 LDL^T 기반 JARVIS 탄성 텐서 심층 분해 (부동소수점 경계 단축 미사용)."""
    with open(DATA_DIR / "jdft_3d.json", "r", encoding="utf-8") as f:
        jdata = json.load(f)

    non_pd_bins = {
        "mild_0_to_minus10": 0,
        "moderate_minus10_to_minus50": 0,
        "severe_minus50_to_minus1000": 0,
        "extreme_lt_minus1000": 0,
    }
    pd_sym_gt1 = 0
    pd_sym_gt5 = 0
    pd_sym_fixed_gt1 = 0
    pd_asym_gt1 = 0
    pd_cubic_total = 0
    pd_cubic_rot_gt1 = 0
    pd_cubic_rot_gt5 = 0
    pd_lmin_v: List[float] = []
    pd_lmin_m: List[float] = []
    pd_mandel_exact_1 = 0
    pd_mandel_exact_5 = 0
    pd_mandel_exact_10 = 0
    n_pd = 0
    n_non_pd = 0
    n_skipped = 0

    for d in jdata:
        et = d.get("elastic_tensor")
        if not isinstance(et, list) or len(et) == 0:
            continue
        try:
            arr = np.asarray(et, dtype=np.float64)
            if arr.shape != (6, 6) or not np.all(np.isfinite(arr)):
                n_skipped += 1
                continue
        except Exception:
            n_skipped += 1
            continue
        spg_raw = d.get("spg_number")
        try:
            spg = int(spg_raw)
        except Exception:
            spg = None
        sym = compute_voigt_symmetry_violations(arr, spg, convention="vasp")
        lv = float(sym["lambda_min_voigt_gpa"])
        lm = float(sym["lambda_min_mandel_gpa"])

        # 전수 정확 유리수 대칭 행렬 LDL^T 판별 (부동소수점 단축 없음)
        C_q = [[to_fraction(et[i][j]) for j in range(6)] for i in range(6)]
        C_sym = [[(C_q[i][j] + C_q[j][i]) / 2 for j in range(6)] for i in range(6)]
        is_pd, _, _, _ = exact_ldlt_or_counterexample(C_sym)

        if is_pd:
            n_pd += 1
            pd_lmin_v.append(lv)
            pd_lmin_m.append(lm)
            for delta_int in (1, 5, 10):
                C_ms = weighted_shift_matrix_exact(C_sym, Fraction(delta_int, 1), MANDEL_WEIGHTS)
                ok_m, _, _, _ = exact_ldlt_or_counterexample(C_ms)
                if ok_m:
                    if delta_int == 1:
                        pd_mandel_exact_1 += 1
                    elif delta_int == 5:
                        pd_mandel_exact_5 += 1
                    elif delta_int == 10:
                        pd_mandel_exact_10 += 1
                else:
                    break
            if sym["max_voigt_violation_gpa"] > 1.0:
                pd_sym_gt1 += 1
            if sym["max_voigt_violation_gpa"] > 5.0:
                pd_sym_gt5 += 1
            if sym["max_voigt_violation_fixed_std_gpa"] > 1.0:
                pd_sym_fixed_gt1 += 1
            if sym["max_asymmetry_gpa"] > 1.0:
                pd_asym_gt1 += 1
            if sym["crystal_system"] == "cubic" and sym["cubic_mandel_rot_inv_viol_gpa"] is not None:
                pd_cubic_total += 1
                if sym["cubic_mandel_rot_inv_viol_gpa"] > 1.0:
                    pd_cubic_rot_gt1 += 1
                if sym["cubic_mandel_rot_inv_viol_gpa"] > 5.0:
                    pd_cubic_rot_gt5 += 1
        else:
            n_non_pd += 1
            if lv >= -10.0:
                non_pd_bins["mild_0_to_minus10"] += 1
            elif lv >= -50.0:
                non_pd_bins["moderate_minus10_to_minus50"] += 1
            elif lv >= -1000.0:
                non_pd_bins["severe_minus50_to_minus1000"] += 1
            else:
                non_pd_bins["extreme_lt_minus1000"] += 1

    v_arr = np.array(pd_lmin_v, dtype=np.float64)
    m_arr = np.array(pd_lmin_m, dtype=np.float64)
    return {
        "n_pd": n_pd,
        "n_non_pd": n_non_pd,
        "n_malformed_skipped": n_skipped,
        "exact_rational_ldlt_used_for_all": True,
        "non_pd_severity_bins": non_pd_bins,
        "pd_symmetry_violations": {
            "pd_voigt_any_gt_1gpa": pd_sym_gt1,
            "pd_voigt_any_gt_1gpa_pct": round(100.0 * pd_sym_gt1 / max(n_pd, 1), 3),
            "pd_voigt_any_gt_5gpa": pd_sym_gt5,
            "pd_voigt_any_gt_5gpa_pct": round(100.0 * pd_sym_gt5 / max(n_pd, 1), 3),
            "pd_voigt_fixed_std_gt_1gpa": pd_sym_fixed_gt1,
            "pd_matrix_asym_gt_1gpa": pd_asym_gt1,
            "pd_cubic_total": pd_cubic_total,
            "pd_cubic_mandel_rot_gt_1gpa": pd_cubic_rot_gt1,
            "pd_cubic_mandel_rot_gt_1gpa_pct": round(100.0 * pd_cubic_rot_gt1 / max(pd_cubic_total, 1), 3),
            "pd_cubic_mandel_rot_gt_5gpa": pd_cubic_rot_gt5,
        },
        "pd_voigt_vs_mandel_exact_rational_gpa": {
            "voigt_p10": float(np.percentile(v_arr, 10)) if len(v_arr) else 0.0,
            "voigt_p50": float(np.percentile(v_arr, 50)) if len(v_arr) else 0.0,
            "voigt_p90": float(np.percentile(v_arr, 90)) if len(v_arr) else 0.0,
            "mandel_p10": float(np.percentile(m_arr, 10)) if len(m_arr) else 0.0,
            "mandel_p50": float(np.percentile(m_arr, 50)) if len(m_arr) else 0.0,
            "mandel_p90": float(np.percentile(m_arr, 90)) if len(m_arr) else 0.0,
            "mandel_exact_robust_1gpa": pd_mandel_exact_1,
            "mandel_exact_robust_5gpa": pd_mandel_exact_5,
            "mandel_exact_robust_10gpa": pd_mandel_exact_10,
        },
    }


def _run_proxy_cv(records: List[Dict[str, Any]], folds: List[np.ndarray], split_name: str) -> Dict[str, Any]:
    """외부 프록시 점수(margin / 2σ_x)에 대한 5-Fold CV + 잔차 커버리지 + ΔAUC 95% CI를 산출한다."""
    n = len(records)
    oos_scores_unif = np.zeros(n, dtype=np.float64)
    oos_scores_lit = np.zeros(n, dtype=np.float64)
    oos_scores_emp_mae = np.zeros(n, dtype=np.float64)
    oos_scores_emp_p75 = np.zeros(n, dtype=np.float64)
    oos_scores_logreg_0 = np.zeros(n, dtype=np.float64)
    oos_scores_logreg_25 = np.zeros(n, dtype=np.float64)
    y0 = np.array([r["flip0"] for r in records], dtype=np.int64)
    y25 = np.array([r["flip25"] for r in records], dtype=np.int64)
    groups = [r["chem_sys"] for r in records]

    # 마진 + 화학군 원핫 피처 행렬 (Claude S5 베이스라인: [1, log1p(margin), onehot(class)])
    cls_vocab = sorted({r["cls"] for r in records})
    cls_to_idx = {c: idx for idx, c in enumerate(cls_vocab)}
    X_feat = np.zeros((n, 2 + len(cls_vocab)), dtype=np.float64)
    X_feat[:, 0] = 1.0
    for i, r in enumerate(records):
        X_feat[i, 1] = math.log1p(max(0.0, r["margin_mev"]))
        X_feat[i, 2 + cls_to_idx[r["cls"]]] = 1.0

    # OOS 잔차 커버리지 추적 (훈련 폴드 δμ 로 평가 폴드 잔차 η_val 직접 계산)
    cov_lit_hits = 0
    cov_mae_hits = 0
    cov_p75_hits = 0
    cov_p90_hits = 0
    cov_by_class: Dict[str, Dict[str, int]] = {}

    fold_aucs_0 = []
    fold_aucs_25 = []
    for k in range(len(folds)):
        val_idx = folds[k]
        tr_idx = np.concatenate([folds[j] for j in range(len(folds)) if j != k])
        tr_comps = [records[i]["comp"] for i in tr_idx]
        tr_deltas = [records[i]["delta_fe"] for i in tr_idx]
        dec = decompose_reference_and_residual_errors(tr_comps, tr_deltas)
        dmu_map = dec["elemental_shifts_ev"]
        cls_mae = {c: st["mae_mev"] for c, st in dec["class_residual_stats"].items()}
        cls_p75 = {c: st["p75_mev"] for c, st in dec["class_residual_stats"].items()}
        cls_p90 = {c: st["p90_mev"] for c, st in dec["class_residual_stats"].items()}
        fallback_mae = dec["residual_mae_mev"]

        for i in val_idx:
            r = records[i]
            m = r["margin_mev"]
            oos_scores_unif[i] = -(0.5 * m)
            oos_scores_lit[i] = -(m / (2.0 * r["sigma_lit_mev"]))
            sig_mae = cls_mae.get(r["cls"], fallback_mae)
            sig_p75 = cls_p75.get(r["cls"], fallback_mae * 1.35)
            sig_p90 = cls_p90.get(r["cls"], fallback_mae * 2.0)
            oos_scores_emp_mae[i] = -(m / (2.0 * sig_mae))
            oos_scores_emp_p75[i] = -(m / (2.0 * sig_p75))

            # 평가 폴드에서의 실제 OOS 잔차 |η_val| 계산 (훈련 폴드 δμ 적용)
            pred_shift = sum(frac * dmu_map.get(el, 0.0) for el, frac in r["comp"].items())
            abs_eta_mev = abs(r["delta_fe"] - pred_shift) * 1000.0
            c_rec = cov_by_class.setdefault(r["cls"], {"n": 0, "lit": 0, "mae": 0, "p75": 0, "p90": 0})
            c_rec["n"] += 1
            if abs_eta_mev <= r["sigma_lit_mev"]:
                cov_lit_hits += 1
                c_rec["lit"] += 1
            if abs_eta_mev <= sig_mae:
                cov_mae_hits += 1
                c_rec["mae"] += 1
            if abs_eta_mev <= sig_p75:
                cov_p75_hits += 1
                c_rec["p75"] += 1
            if abs_eta_mev <= sig_p90:
                cov_p90_hits += 1
                c_rec["p90"] += 1

        # 마진 + 화학군 원핫 지도학습 로지스틱 베이스라인 (훈련 폴드만 적합)
        oos_scores_logreg_0[val_idx] = _fit_logistic_margin_onehot(
            X_feat[tr_idx], y0[tr_idx].astype(np.float64), X_feat[val_idx]
        )
        oos_scores_logreg_25[val_idx] = _fit_logistic_margin_onehot(
            X_feat[tr_idx], y25[tr_idx].astype(np.float64), X_feat[val_idx]
        )

        fold_aucs_0.append({
            "unif": round(_roc_auc(y0[val_idx], oos_scores_unif[val_idx]), 4),
            "lit_hetero_proxy": round(_roc_auc(y0[val_idx], oos_scores_lit[val_idx]), 4),
            "oos_emp_mae_proxy": round(_roc_auc(y0[val_idx], oos_scores_emp_mae[val_idx]), 4),
            "margin_plus_class_onehot_logreg": round(_roc_auc(y0[val_idx], oos_scores_logreg_0[val_idx]), 4),
        })
        fold_aucs_25.append({
            "unif": round(_roc_auc(y25[val_idx], oos_scores_unif[val_idx]), 4),
            "lit_hetero_proxy": round(_roc_auc(y25[val_idx], oos_scores_lit[val_idx]), 4),
            "oos_emp_mae_proxy": round(_roc_auc(y25[val_idx], oos_scores_emp_mae[val_idx]), 4),
            "margin_plus_class_onehot_logreg": round(_roc_auc(y25[val_idx], oos_scores_logreg_25[val_idx]), 4),
        })

    rob_mask = (-oos_scores_emp_mae) >= 1.0
    frg_mask = ~rob_mask
    rob_n, frg_n = int(rob_mask.sum()), int(frg_mask.sum())
    rob_f0, frg_f0 = int(y0[rob_mask].sum()), int(y0[frg_mask].sum())
    rob_f25, frg_f25 = int(y25[rob_mask].sum()), int(y25[frg_mask].sum())

    cov_class_pct = {
        cls: {
            "count": st["n"],
            "lit_profile_cov_pct": round(100.0 * st["lit"] / max(st["n"], 1), 2),
            "oos_mae_cov_pct": round(100.0 * st["mae"] / max(st["n"], 1), 2),
            "oos_p75_cov_pct": round(100.0 * st["p75"] / max(st["n"], 1), 2),
            "oos_p90_cov_pct": round(100.0 * st["p90"] / max(st["n"], 1), 2),
        }
        for cls, st in sorted(cov_by_class.items())
    }

    return {
        "split_scheme": split_name,
        "is_certified_lp": False,
        "n_evaluated": n,
        "pooled_oos_roc_auc_flip_gt0": {
            "uniform_proxy": round(_roc_auc(y0, oos_scores_unif), 4),
            "literature_hetero_proxy": round(_roc_auc(y0, oos_scores_lit), 4),
            "oos_emp_mae_proxy": round(_roc_auc(y0, oos_scores_emp_mae), 4),
            "oos_emp_p75_proxy": round(_roc_auc(y0, oos_scores_emp_p75), 4),
            "margin_plus_class_onehot_logreg": round(_roc_auc(y0, oos_scores_logreg_0), 4),
            "delta_emp_mae_vs_uniform_cluster_boot": _paired_bootstrap_delta_auc(
                y0, oos_scores_emp_mae, oos_scores_unif, groups=groups, n_boot=1000
            ),
        },
        "pooled_oos_roc_auc_flip_gt25": {
            "uniform_proxy": round(_roc_auc(y25, oos_scores_unif), 4),
            "literature_hetero_proxy": round(_roc_auc(y25, oos_scores_lit), 4),
            "oos_emp_mae_proxy": round(_roc_auc(y25, oos_scores_emp_mae), 4),
            "oos_emp_p75_proxy": round(_roc_auc(y25, oos_scores_emp_p75), 4),
            "margin_plus_class_onehot_logreg": round(_roc_auc(y25, oos_scores_logreg_25), 4),
            "delta_emp_mae_vs_uniform_cluster_boot": _paired_bootstrap_delta_auc(
                y25, oos_scores_emp_mae, oos_scores_unif, groups=groups, n_boot=1000
            ),
        },
        "oos_emp_mae_proxy_threshold_1x": {
            "low_risk_count": rob_n,
            "low_risk_flip_gt0_pct": round(100.0 * rob_f0 / max(rob_n, 1), 3),
            "high_risk_count": frg_n,
            "high_risk_flip_gt0_pct": round(100.0 * frg_f0 / max(frg_n, 1), 3),
            "relative_risk_gt0": _safe_rr(frg_f0, frg_n, rob_f0, rob_n),
            "low_risk_flip_gt25_pct": round(100.0 * rob_f25 / max(rob_n, 1), 3),
            "high_risk_flip_gt25_pct": round(100.0 * frg_f25 / max(frg_n, 1), 3),
            "relative_risk_gt25": _safe_rr(frg_f25, frg_n, rob_f25, rob_n),
        },
        "oos_residual_interval_coverage": {
            "overall_lit_profile_cov_pct": round(100.0 * cov_lit_hits / max(n, 1), 2),
            "overall_oos_mae_cov_pct": round(100.0 * cov_mae_hits / max(n, 1), 2),
            "overall_oos_p75_cov_pct": round(100.0 * cov_p75_hits / max(n, 1), 2),
            "overall_oos_p90_cov_pct": round(100.0 * cov_p90_hits / max(n, 1), 2),
            "by_chemistry_class": cov_class_pct,
        },
        "five_fold_aucs_flip_gt0": fold_aucs_0,
        "five_fold_aucs_flip_gt25": fold_aucs_25,
    }


def analyze_gnome_oos_calibration() -> Dict[str, Any]:
    """117,043개 매칭 GNoME PBE-r2SCAN 결정에 대해
    (1) 외부 프록시 무작위 5-Fold 및 화학계 GroupKFold 교차검증 + 잔차 커버리지 + 보정 곡선,
    (2) 실제 정확 Charnes-Cooper 이질적 LP 의 화학계 GroupKFold held-out 교차검증을 수행한다.
    """
    pbe_map: Dict[str, Tuple[str, float, float]] = {}
    n_pbe_drop = 0
    with open(DATA_DIR / "gnome_stable_materials_summary.csv", "r", encoding="utf-8") as f:
        for r in csv.DictReader(f):
            try:
                pbe_map[r["MaterialId"]] = (
                    r["Formation Energy Per Atom"],
                    float(r["Formation Energy Per Atom"]),
                    float(r["Decomposition Energy Per Atom"]) if r["Decomposition Energy Per Atom"] else float("nan"),
                )
            except Exception:
                n_pbe_drop += 1

    records = []
    matched_pbe_entries: List[PhaseEntry] = []
    matched_r2_entries: List[PhaseEntry] = []
    n_r2_drop = 0
    with open(DATA_DIR / "gnome_stable_materials_r2scan.csv", "r", encoding="utf-8") as f:
        for r in csv.DictReader(f):
            mid = r["MaterialId"]
            if mid not in pbe_map:
                continue
            try:
                r2_fe_str = r["Formation Energy Per Atom"]
                r2_fe = float(r2_fe_str)
                r2_de = float(r["Decomposition Energy Per Atom"]) if r["Decomposition Energy Per Atom"] else float("nan")
                pbe_fe_str, pbe_fe, pbe_de = pbe_map[mid]
                comp = formula_to_atom_fractions(r["Composition"])
                cls = classify_chemistry(comp.keys())
                matched_pbe_entries.append(PhaseEntry(mid, r["Composition"], comp, to_fraction(pbe_fe_str)))
                matched_r2_entries.append(PhaseEntry(mid, r["Composition"], comp, to_fraction(r2_fe_str)))
                if math.isfinite(pbe_de) and math.isfinite(r2_de) and pbe_de <= 0.0:
                    records.append({
                        "id": mid,
                        "comp": {el: float(q) for el, q in comp.items()},
                        "chem_sys": tuple(sorted(comp.keys())),
                        "cls": cls,
                        "delta_fe": r2_fe - pbe_fe,
                        "margin_mev": -pbe_de * 1000.0,
                        "flip0": 1 if r2_de > 0.0 else 0,
                        "flip25": 1 if r2_de > 0.025 else 0,
                        "sigma_lit_mev": float(getattr(HETERO_CHEM_PROFILE, cls)) * 1000.0,
                    })
            except Exception:
                n_r2_drop += 1

    # (A) 외부 프록시 무작위 5-Fold 및 화학계 GroupKFold
    n = len(records)
    rng = np.random.default_rng(2026)
    rand_folds = np.array_split(rng.permutation(n), 5)
    grp_folds = _group_kfold_indices([r["chem_sys"] for r in records], n_splits=5, seed=2026)

    proxy_random = _run_proxy_cv(records, rand_folds, "random_5fold")
    proxy_grouped = _run_proxy_cv(records, grp_folds, "chemical_system_group_5fold")

    # 명목 여유 구간별 실제 r2SCAN 전복률 보정 곡선 (Calibration Curve)
    bins = [(0, 10), (10, 20), (20, 35), (35, 50), (50, 100), (100, 200), (200, 1e9)]
    calib = []
    for lo, hi in bins:
        sub = [r for r in records if lo <= r["margin_mev"] < hi]
        if not sub:
            continue
        f0 = sum(r["flip0"] for r in sub)
        f25 = sum(r["flip25"] for r in sub)
        calib.append({
            "pbe_margin_bin_mev": f"{lo}-{int(hi) if hi < 1e8 else 'inf'}",
            "eps_unif_bin_mev": f"{lo/2:.0f}-{hi/2:.0f}" if hi < 1e8 else "100-inf",
            "count": len(sub),
            "flip_gt0_pct": round(100.0 * f0 / len(sub), 2),
            "flip_gt25_pct": round(100.0 * f25 / len(sub), 2),
        })

    # (B) 실제 정확 Charnes-Cooper 이질적 LP 의 화학계 GroupKFold Held-Out 검증
    # (117,043개 매칭 결정 중 결정론적 10% 표본 11,704개의 화학계를 5-Fold GroupKFold로 분할하고,
    #  각 폴드의 훈련 화학계에서 추정한 화학군별 잔차 σ_OOS 를 실제 Charnes-Cooper LP 에 투입해 평가!)
    idx_pbe = PhaseDiagramIndex(matched_pbe_entries, add_elemental_refs=True)
    idx_r2 = PhaseDiagramIndex(matched_r2_entries, add_elemental_refs=True)
    r2_entry_by_id = {p.material_id: p for p in matched_r2_entries}

    # 화학계 기준 5-Fold 분할 (전체 117,043개에서 훈련, 평가 시 각 폴드에서 2,000개씩 총 10,000개 정확 LP 평가)
    all_groups = [tuple(sorted(p.elements)) for p in matched_pbe_entries]
    all_grp_folds = _group_kfold_indices(all_groups, n_splits=5, seed=2026)

    lp_y0: List[int] = []
    lp_y25: List[int] = []
    lp_groups: List[Tuple[str, ...]] = []
    lp_sc_unif: List[float] = []
    lp_sc_lit: List[float] = []
    lp_sc_lit_zero_elem: List[float] = []
    lp_sc_oos_mae: List[float] = []
    lp_sc_oos_zero_elem: List[float] = []
    lp_oos_rob_f0, lp_oos_rob_n = 0, 0
    lp_oos_frg_f0, lp_oos_frg_n = 0, 0
    lp_ze_rob_f0, lp_ze_rob_n = 0, 0
    lp_ze_frg_f0, lp_ze_frg_n = 0, 0

    for k in range(5):
        val_idx = all_grp_folds[k]
        tr_idx = np.concatenate([all_grp_folds[j] for j in range(5) if j != k])
        tr_comps = [{el: float(q) for el, q in matched_pbe_entries[i].comp.items()} for i in tr_idx]
        tr_deltas = [
            float(matched_r2_entries[i].energy_per_atom - matched_pbe_entries[i].energy_per_atom)
            for i in tr_idx
        ]
        dec = decompose_reference_and_residual_errors(tr_comps, tr_deltas)
        oos_sigma: Dict[str, Fraction] = {
            "elemental_ref": Fraction(10, 1000),
        }
        oos_sigma_zero_elem: Dict[str, Fraction] = {
            "elemental_ref": Fraction(0, 1),
        }
        for cls, st in dec["class_residual_stats"].items():
            # meV -> 정확한 유리수 eV (소수 3자리 반올림으로 깔끔한 유리수 가중치)
            q_w = Fraction(max(1, int(round(st["mae_mev"] * 10))), 10000)
            oos_sigma[cls] = q_w
            if cls != "elemental_ref":
                oos_sigma_zero_elem[cls] = q_w

        # 평가 폴드에서 결정론적 균등 간격 2,000개 표본 추출 -> 실제 Charnes-Cooper LP 실행
        step = max(1, len(val_idx) // 2000)
        for i in val_idx[::step][:2000]:
            p_pbe = matched_pbe_entries[int(i)]
            p_r2 = r2_entry_by_id[p_pbe.material_id]
            comp_pbe = idx_pbe.get_competing_phases(p_pbe)
            comp_r2 = idx_r2.get_competing_phases(p_r2)
            if not comp_pbe or not comp_r2:
                continue
            rec_lit = audit_single_phase(p_pbe, comp_pbe, emit_certificate=False)
            if not rec_lit.is_nominally_stable:
                continue
            rec_lit_ze = audit_single_phase(
                p_pbe, comp_pbe, hetero_profile=HETERO_CHEM_ZERO_ELEM_PROFILE, emit_certificate=False
            )
            rec_oos = audit_single_phase(p_pbe, comp_pbe, custom_class_sigma=oos_sigma, emit_certificate=False)
            rec_oos_ze = audit_single_phase(
                p_pbe, comp_pbe, custom_class_sigma=oos_sigma_zero_elem, emit_certificate=False
            )
            rec_r2 = audit_single_phase(p_r2, comp_r2, emit_certificate=False)

            f0 = 0 if rec_r2.is_nominally_stable else 1
            f25 = 1 if rec_r2.nominal_ehull_mev > 25.0 else 0
            lp_y0.append(f0)
            lp_y25.append(f25)
            lp_groups.append(tuple(sorted(p_pbe.elements)))
            lp_sc_unif.append(-rec_lit.eps_uniform_mev)
            lp_sc_lit.append(-rec_lit.hetero_critical_scale)
            lp_sc_lit_zero_elem.append(-rec_lit_ze.hetero_critical_scale)
            lp_sc_oos_mae.append(-rec_oos.hetero_critical_scale)
            lp_sc_oos_zero_elem.append(-rec_oos_ze.hetero_critical_scale)
            if rec_oos.status_hetero == "Certified_Robust_Stable":
                lp_oos_rob_n += 1
                lp_oos_rob_f0 += f0
            else:
                lp_oos_frg_n += 1
                lp_oos_frg_f0 += f0
            if rec_oos_ze.status_hetero == "Certified_Robust_Stable":
                lp_ze_rob_n += 1
                lp_ze_rob_f0 += f0
            else:
                lp_ze_frg_n += 1
                lp_ze_frg_f0 += f0

    arr_y0 = np.asarray(lp_y0, dtype=np.int64)
    arr_y25 = np.asarray(lp_y25, dtype=np.int64)
    arr_u = np.asarray(lp_sc_unif, dtype=np.float64)
    arr_l = np.asarray(lp_sc_lit, dtype=np.float64)
    arr_lze = np.asarray(lp_sc_lit_zero_elem, dtype=np.float64)
    arr_o = np.asarray(lp_sc_oos_mae, dtype=np.float64)
    arr_oze = np.asarray(lp_sc_oos_zero_elem, dtype=np.float64)

    exact_lp_group_cv = {
        "split_scheme": "chemical_system_group_5fold_exact_charnes_cooper_lp",
        "evaluation_regime": "transductive_fixed_catalog_hull_heldout_sigma_calibration",
        "is_certified_lp": True,
        "n_pbe_stable_evaluated": int(len(arr_y0)),
        "n_unique_chemical_systems_evaluated": len(set(lp_groups)),
        "n_flipped_gt0": int(arr_y0.sum()),
        "n_flipped_gt25": int(arr_y25.sum()),
        "roc_auc_flip_gt0": {
            "uniform_exact_lp": round(_roc_auc(arr_y0, arr_u), 4),
            "literature_hetero_exact_lp": round(_roc_auc(arr_y0, arr_l), 4),
            "literature_hetero_zero_elem_exact_lp": round(_roc_auc(arr_y0, arr_lze), 4),
            "oos_emp_mae_exact_lp": round(_roc_auc(arr_y0, arr_o), 4),
            "oos_emp_mae_zero_elem_exact_lp": round(_roc_auc(arr_y0, arr_oze), 4),
            "delta_oos_vs_uniform_cluster_boot": _paired_bootstrap_delta_auc(
                arr_y0, arr_o, arr_u, groups=lp_groups, n_boot=1000
            ),
            "delta_oos_zero_elem_vs_uniform_cluster_boot": _paired_bootstrap_delta_auc(
                arr_y0, arr_oze, arr_u, groups=lp_groups, n_boot=1000
            ),
        },
        "roc_auc_flip_gt25": {
            "uniform_exact_lp": round(_roc_auc(arr_y25, arr_u), 4),
            "literature_hetero_exact_lp": round(_roc_auc(arr_y25, arr_l), 4),
            "literature_hetero_zero_elem_exact_lp": round(_roc_auc(arr_y25, arr_lze), 4),
            "oos_emp_mae_exact_lp": round(_roc_auc(arr_y25, arr_o), 4),
            "oos_emp_mae_zero_elem_exact_lp": round(_roc_auc(arr_y25, arr_oze), 4),
            "delta_oos_vs_uniform_cluster_boot": _paired_bootstrap_delta_auc(
                arr_y25, arr_o, arr_u, groups=lp_groups, n_boot=1000
            ),
            "delta_oos_zero_elem_vs_uniform_cluster_boot": _paired_bootstrap_delta_auc(
                arr_y25, arr_oze, arr_u, groups=lp_groups, n_boot=1000
            ),
        },
        "oos_exact_lp_threshold_1x": {
            "robust_count": lp_oos_rob_n,
            "robust_flip_gt0_pct": round(100.0 * lp_oos_rob_f0 / max(lp_oos_rob_n, 1), 3),
            "fragile_count": lp_oos_frg_n,
            "fragile_flip_gt0_pct": round(100.0 * lp_oos_frg_f0 / max(lp_oos_frg_n, 1), 3),
            "relative_risk_gt0": _safe_rr(lp_oos_frg_f0, lp_oos_frg_n, lp_oos_rob_f0, lp_oos_rob_n),
        },
        "oos_exact_lp_zero_elem_ablation_threshold_1x": {
            "robust_count": lp_ze_rob_n,
            "robust_flip_gt0_pct": round(100.0 * lp_ze_rob_f0 / max(lp_ze_rob_n, 1), 3),
            "fragile_count": lp_ze_frg_n,
            "fragile_flip_gt0_pct": round(100.0 * lp_ze_frg_f0 / max(lp_ze_frg_n, 1), 3),
            "relative_risk_gt0": _safe_rr(lp_ze_frg_f0, lp_ze_frg_n, lp_ze_rob_f0, lp_ze_rob_n),
        },
    }

    return {
        "n_pbe_stable_matched_external_proxy": n,
        "n_unique_chemical_systems": len({r["chem_sys"] for r in records}),
        "n_dropped_parse": {"pbe": n_pbe_drop, "r2scan": n_r2_drop},
        "external_proxy_random_5fold": proxy_random,
        "external_proxy_chemical_system_group_5fold": proxy_grouped,
        "exact_charnes_cooper_lp_chemical_system_group_5fold": exact_lp_group_cv,
        "margin_calibration_curve": calib,
    }


_ABL_INDEX: Optional[PhaseDiagramIndex] = None


def _init_jarvis_abl_worker(pruned_by_elem_set: Dict[frozenset, List[PhaseEntry]]) -> None:
    global _ABL_INDEX
    _set_below_normal_priority()
    idx = PhaseDiagramIndex.__new__(PhaseDiagramIndex)
    idx.phases = []
    idx.by_elem_set = pruned_by_elem_set
    idx.all_elements = set()
    idx._pruned_by_elem_set = pruned_by_elem_set
    idx.prune_polymorphs = True
    idx.injected_elemental_refs = []
    idx.negative_elemental_phases = []
    _ABL_INDEX = idx


def _jarvis_abl_chunk(chunk: List[PhaseEntry]) -> List[Tuple[bool, str, str, bool, bool]]:
    assert _ABL_INDEX is not None
    out: List[Tuple[bool, str, str, bool, bool]] = []
    for p in chunk:
        comps = _ABL_INDEX.get_competing_phases(p)
        if not comps:
            continue
        r_std = audit_single_phase(p, comps, hetero_profile=HETERO_CHEM_PROFILE, emit_certificate=False)
        r_ze = audit_single_phase(p, comps, hetero_profile=HETERO_CHEM_ZERO_ELEM_PROFILE, emit_certificate=False)
        out.append((r_std.is_nominally_stable, r_std.status_hetero, r_ze.status_hetero, r_std.phase_switching, r_ze.phase_switching))
    return out


def analyze_jarvis_zero_elem_ablation(workers: int = 2) -> Dict[str, Any]:
    """JARVIS-DFT 3D 전수(93,901 경쟁상 보유 결정)에 대한 원소 기준 잔차 σ_elem=0 절제 실험(Claude P3 대응)."""
    with open(DATA_DIR / "jdft_3d.json", "r", encoding="utf-8") as f:
        jdata = json.load(f)
    phases: List[PhaseEntry] = []
    for d in jdata:
        fe = d.get("formation_energy_peratom")
        form = d.get("formula")
        if fe in (None, "na") or not form:
            continue
        try:
            fe_f = float(fe)
            if not math.isfinite(fe_f):
                continue
            comp = formula_to_atom_fractions(form)
            phases.append(PhaseEntry(d["jid"], form, comp, to_fraction(fe)))
        except Exception:
            continue
    idx = PhaseDiagramIndex(phases, add_elemental_refs=True)
    chunks = [phases[i : i + 500] for i in range(0, len(phases), 500)]
    rows: List[Tuple[bool, str, str, bool, bool]] = []
    with ProcessPoolExecutor(
        max_workers=workers,
        initializer=_init_jarvis_abl_worker,
        initargs=(idx._pruned_by_elem_set,),
    ) as ex:
        for ch in ex.map(_jarvis_abl_chunk, chunks):
            rows.extend(ch)

    nom_stab = [r for r in rows if r[0]]
    n_stab = len(nom_stab)
    std_rob = sum(1 for r in nom_stab if r[1] == "Certified_Robust_Stable")
    ze_rob = sum(1 for r in nom_stab if r[2] == "Certified_Robust_Stable")
    std_frg = sum(1 for r in nom_stab if r[1] == "Fragile")
    ze_frg = sum(1 for r in nom_stab if r[2] == "Fragile")
    std_sw = sum(1 for r in nom_stab if r[3])
    ze_sw = sum(1 for r in nom_stab if r[4])
    return {
        "n_competed_audited": len(rows),
        "n_nom_stable": n_stab,
        "sigma_elem_10mev_default": {
            "robust_stable": std_rob,
            "fragile": std_frg,
            "fragile_pct": round(100.0 * std_frg / max(n_stab, 1), 2),
            "phase_switching": std_sw,
        },
        "sigma_elem_0mev_ablation": {
            "robust_stable": ze_rob,
            "fragile": ze_frg,
            "fragile_pct": round(100.0 * ze_frg / max(n_stab, 1), 2),
            "phase_switching": ze_sw,
        },
        "delta_fragile_count_when_zero_elem": ze_frg - std_frg,
        "delta_fragile_pct_points": round(100.0 * (ze_frg - std_frg) / max(n_stab, 1), 2),
    }


def _set_keep_awake(enable: bool) -> None:
    """작업 수명 동안만 Windows 시스템 절전을 방지하고 종료 시 원복한다."""
    if os.name != "nt":
        return
    try:
        flag = 0x80000001 if enable else 0x80000000
        ctypes.windll.kernel32.SetThreadExecutionState(flag)
    except Exception:
        pass


def _set_below_normal_priority() -> None:
    """Windows 환경에서 프로세스 우선순위를 BelowNormal로 낮춰 데스크톱 응답성을 보호한다."""
    if os.name != "nt":
        return
    try:
        handle = ctypes.windll.kernel32.GetCurrentProcess()
        ctypes.windll.kernel32.SetPriorityClass(handle, 0x00004000)
    except Exception:
        pass


def main() -> None:
    parser = argparse.ArgumentParser(description="CertMat 심층 보완 분석 (탄성 심층 분해, σ_elem=0 절제, GNoME OOS 5-Fold)")
    parser.add_argument(
        "--workers",
        type=int,
        default=2,
        help="병렬 워커 수 (안전 기본값: 2; 유휴 시 명시 조정 가능)",
    )
    args = parser.parse_args()
    workers = max(1, int(args.workers))

    print(f"Running deep supplementary analysis (workers={workers})...")
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    _set_below_normal_priority()
    _set_keep_awake(True)
    try:
        res = {
            "jarvis_elastic_deep": analyze_jarvis_elastic_deep(),
            "jarvis_zero_elem_ablation": analyze_jarvis_zero_elem_ablation(workers=workers),
            "gnome_oos_5fold_calibration": analyze_gnome_oos_calibration(),
        }
    finally:
        _set_keep_awake(False)
    out_path = RESULTS_DIR / "supplementary_analysis.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(res, f, indent=2, ensure_ascii=False)
    print(json.dumps(res, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
