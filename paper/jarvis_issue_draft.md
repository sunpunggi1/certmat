# GitHub Issue Draft for `usnistgov/jarvis`

**Proposed Title:**
`[Data Integrity] Published ehull values in jdft_3d-9-24-2025.json appear inflated by an extra 1/N_fu division on optb88vdw_total_energy`

---

Hello JARVIS-DFT maintainers,

Thank you very much for maintaining JARVIS-DFT and `jarvis-tools`. While performing an automated exact convex-hull audit across the latest Figshare 3D release (performed via AI-assisted exact rational verification with a compiled Lean 4 checker and cross-checked with a standalone pure-Python script), we noticed a systematic discrepancy in the published `ehull` field that affects the majority of multinary entries in the JSON snapshot. We wanted to report our exact findings along with a minimal reproduction script so you can verify whether an upstream unit-conversion step divided per-atom `optb88vdw_total_energy` a second time by the reduced formula-unit atom count $N_{\text{fu}}$.

### 1. Affected Snapshot
- **Dataset:** Figshare Article `6815699` (`dft_3d`)
- **Archive & File:** `jdft_3d.json.zip` -> `jdft_3d-9-24-2025.json` (Figshare File ID `64391379`)
- **Extracted JSON SHA-256:** `9dacb55ac8371c7c2bf0332933b55c98e9cca6201e92eb9d6fcd03aab0975907`
- **Total entries with finite `ehull`:** `93,902`

### 2. Summary of Observed Discrepancy
- Across all `93,902` entries, the median published `ehull` is **`1.7189 eV/atom`**, with **`73,558` entries (`78.33%`)** showing `ehull > 0.5 eV/atom` and **`63,386` entries (`67.50%`)** showing `ehull > 1.0 eV/atom`.
- Even among the **`25,908`** compounds that lie on the exact OptB88vdW convex hull reconstructed from `formation_energy_peratom` (and identically from raw `optb88vdw_total_energy`, median agreement `0.005 meV/atom`), **`16,898` (`65.22%`)** have published `ehull > 1.0 eV/atom` (median `1.6118 eV/atom`).
- By contrast, single-element entries ($N_{\text{fu}} = 1$, `n = 915`) are unaffected and have a median published `ehull` of **`0.0317 eV/atom`**.
- On all **`92,955`** multinary entries ($N_{\text{fu}} > 1$), the formula
  $$\hat{e}_{\text{bug}} = \frac{\texttt{optb88vdw\_total\_energy}}{N_{\text{fu}}} - \sum_{e} x_e E^{\text{min,elem}}_{\text{optB88}}(e)$$
  (where $x_e$ is the atomic fraction and $E^{\text{min,elem}}_{\text{optB88}}(e)$ is the lowest single-atom `optb88vdw_total_energy` for element $e$ in the dataset) reproduces the published `ehull` with a **median absolute residual of `0.00677 eV/atom`**, matching within `0.01 eV/atom` for `66.69%` (`61,990`) and within `0.05 eV/atom` for `84.72%` (`78,751`) of all multinary compounds.

| Forensic Check (`n = 92,955` multinaries) | Median Abs. Residual vs. Published `ehull` | Match `< 0.01 eV` | Match `< 0.05 eV` |
| :--- | ---: | ---: | ---: |
| **Double-division hypothesis (`optb88vdw_total_energy / N_fu - E_elem`)** | **`0.00677 eV/atom`** | **`66.69%`** | **`84.72%`** |
| Negative control 1 (no extra `1 / N_fu` division) | `2.60472 eV/atom` | `0.18%` | `0.95%` |
| Negative control 2 (permuted elemental references) | `2.10779 eV/atom` | `0.22%` | `1.20%` |

### 3. Representative Stable Ground-State Examples (`abs_diff = 0.00000 eV`)
All five compounds below have negative `formation_energy_peratom`, sit strictly on the reconstructed OptB88vdW convex hull with `27-146 meV/atom` stability margin, yet report `ehull > 1.1 eV/atom` in `jdft_3d-9-24-2025.json`:

| `jid` | Formula | $N_{\text{fu}}$ | `formation_energy_peratom` (eV/atom) | `optb88vdw_total_energy` (eV/atom) | Published `ehull` (eV/atom) | `(E_optB88 / N_fu) - E_elem` |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: |
| `JVASP-106708` | `U2Pd3Rh3` | 8 | `-0.67233` | `-4.93522` | `3.6460` | `3.6460` |
| `JVASP-15157` | `TbB2Ru3` | 6 | `-0.45204` | `-5.75129` | `4.3407` | `4.3407` |
| `JVASP-13318` | `BaNd2Se4` | 7 | `-2.02903` | `-3.66370` | `1.1113` | `1.1113` |
| `JVASP-152492` | `TbAlPt` | 3 | `-1.20582` | `-3.75408` | `1.2969` | `1.2969` |
| `JVASP-109512` | `CrGaRu2` | 4 | `-0.15943` | `-4.60243` | `3.2924` | `3.2924` |

### 4. Minimal Reproduction Script

```python
import json, math, re, statistics

def parse_formula(formula: str):
    tokens = re.findall(r"([A-Z][a-z]*)([0-9.]*)", formula)
    counts = {}
    for el, num in tokens:
        counts[el] = counts.get(el, 0.0) + (float(num) if num else 1.0)
    return counts

with open("jdft_3d.json", "r", encoding="utf-8") as f:
    records = json.load(f)

elem_o88 = {}
for r in records:
    o88 = r.get("optb88vdw_total_energy")
    if isinstance(o88, (int, float)) and math.isfinite(o88):
        cnt = parse_formula(r["formula"])
        if len(cnt) == 1 and next(iter(cnt.values())) == 1.0:
            el = next(iter(cnt))
            elem_o88[el] = min(elem_o88.get(el, float("inf")), float(o88))

residuals = []
for r in records:
    eh, o88 = r.get("ehull"), r.get("optb88vdw_total_energy")
    if isinstance(eh, (int, float)) and isinstance(o88, (int, float)) and math.isfinite(eh) and math.isfinite(o88):
        cnt = parse_formula(r["formula"])
        n_fu = sum(cnt.values())
        if len(cnt) > 1 and n_fu > 1.0 and all(el in elem_o88 for el in cnt):
            e_elem = sum((c / n_fu) * elem_o88[el] for el, c in cnt.items())
            residuals.append(abs((o88 / n_fu) - e_elem - eh))

print("Multinaries checked:", len(residuals))
print("Median abs residual (eV/atom):", round(statistics.median(residuals), 5))
print("Share within 0.05 eV/atom:", f"{100.0 * sum(x < 0.05 for x in residuals) / len(residuals):.2f}%")
```

*(A full standalone reproduction script is included in our public repository: [`scripts/repro_jarvis_ehull_bug.py`](https://github.com/sunpunggi1/certmat/blob/main/scripts/repro_jarvis_ehull_bug.py) in [sunpunggi1/certmat](https://github.com/sunpunggi1/certmat).)*

### 5. Suspected Cause & Suggestion
Since `optb88vdw_total_energy` in `jdft_3d-9-24-2025.json` is already normalized per atom, it looks like a post-processing script constructing `ehull` may have divided `optb88vdw_total_energy` by the reduced formula-unit size `N_fu` (treating a per-atom field as if it were per-formula-unit). Recomputing `ehull` directly from `formation_energy_peratom` (or per-atom `optb88vdw_total_energy` without an extra `/ N_fu` factor) restores physically consistent hull distances.

Hope this is helpful! Please let us know if you would like any additional diagnostics.
