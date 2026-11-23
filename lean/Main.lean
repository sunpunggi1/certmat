/-
  Main.lean
  CertMat 독립 실행형 증명서 검증 CLI (`certmat-check`).
  Python 감사 엔진이 출력한 정확한 유리수 증명서 파일(TSV 형식)을 읽어
  `CertMat.Checker`의 검증 함수로 100% 정확하게 재검증한다.

  지원 레코드 형식 (줄 단위 탭 구분):
  1)  DUAL_STABLE             <m> <E> <ex> <delta> <cx...> <c_flat...> <en...> <mu...>
  2)  PRIMAL_UNSTABLE         <m> <E> <ex> <cx...> <c_flat...> <en...> <lam...>
  3)  INTERVAL_STABLE         <m> <E> <ex> <wx> <eps> <delta> <cx...> <c_flat...> <en...> <w...> <mu...>
  4)  INTERVAL_UNSTABLE       <m> <E> <ex> <wx> <eps> <cx...> <c_flat...> <en...> <w...> <lam...>
  5)  INTERVAL_FRAGILE_DESTAB <m> <E> <ex> <wx> <eps> <cx...> <c_flat...> <en...> <w...> <lam...>
  6)  INTERVAL_FRAGILE_STAB   <m> <E> <ex> <wx> <eps> <cx...> <c_flat...> <en...> <w...> <mu...>
  7)  BORN_LDLT               <n> <C_flat...> <L_flat...> <d...>
  8)  BORN_NON_PD             <n> <C_flat...> <v...>
  9)  WEYL_ROBUST             <n> <lam0> <delta> <C_flat...> <L_flat...> <d...>
  10) WEYL_FRAGILE            <n> <delta> <C_flat...> <v...>
  11) MANDEL_WEYL_ROBUST      <lam0> <delta> <C_flat...> <L_flat...> <d...>  (6x6 고정)
  12) MANDEL_WEYL_FRAGILE     <delta> <C_flat...> <v...>                     (6x6 고정)
-/

import CertMat

open CertMat

/-- 엄격 ASCII 자연수 파서 (`^[0-9]+$` 만 허용; '+', '_', 공백 거부) -/
def parseStrictNat (s : String) : Option Nat :=
  if s.isEmpty then none
  else
    let chars := s.toList
    if chars.all (fun c => '0' ≤ c && c ≤ '9') then s.toNat? else none

/-- 엄격 ASCII 정수 파서 (`^-?[0-9]+$` 만 허용; '+', '_', 공백 거부) -/
def parseStrictInt (s : String) : Option Int :=
  match s.toList with
  | [] => none
  | '-' :: rest =>
    if rest.isEmpty then none
    else if rest.all (fun c => '0' ≤ c && c ≤ '9') then s.toInt? else none
  | chars =>
    if chars.all (fun c => '0' ≤ c && c ≤ '9') then s.toInt? else none

/-- 문자열 "p/q" 또는 "p" 를 정확한 유리수 Q 로 엄격 파싱 -/
def parseQ (s : String) : Option Q :=
  match s.splitOn "/" with
  | [numStr] =>
    match parseStrictInt numStr with
    | some n => some (Q.ofInt n)
    | none => none
  | [numStr, denStr] =>
    match parseStrictInt numStr, parseStrictNat denStr with
    | some n, some d =>
      if h : 0 < d then some ⟨n, d, h⟩ else none
    | _, _ => none
  | _ => none

/-- 토큰 배열에서 지정 구간의 유리수 벡터 추출 -/
def parseQArray (tokens : Array String) (start len : Nat) : Option (Array Q) := do
  if start + len > tokens.size then none
  let mut acc : Array Q := Array.mkEmpty len
  for i in [0:len] do
    let q ← parseQ (tokens[start + i]!)
    acc := acc.push q
  return acc

def vecOfArray {n : Nat} (arr : Array Q) (h : arr.size = n) : Fin n → Q :=
  fun i => arr[i.val]'(by omega)

def matOfArray {m n : Nat} (arr : Array Q) (h : arr.size = m * n) : Fin m → Fin n → Q :=
  fun i j =>
    have hlt : i.val * n + j.val < m * n := by
      have hi : i.val + 1 ≤ m := i.isLt
      have hj : j.val < n := j.isLt
      calc i.val * n + j.val < i.val * n + n := Nat.add_lt_add_left hj (i.val * n)
        _ = (i.val + 1) * n := by rw [Nat.succ_mul]
        _ ≤ m * n := Nat.mul_le_mul_right n hi
    arr[i.val * n + j.val]'(by omega)

/-- 단일 레코드 검증 (정확한 필드 개수 엄격 검사로 변조·절단 레코드 원천 차단) -/
def verifyLine (line : String) : Except String Bool := do
  let parts := (line.trim.splitOn "\t").toArray
  if parts.size < 2 then
    throw "malformed certificate line: fewer than 2 tab-separated fields"
  let kind := parts[0]!
  match kind with
  | "DUAL_STABLE" =>
    if parts.size < 5 then throw "truncated DUAL_STABLE header"
    let some m := parseStrictNat parts[1]! | throw "invalid m"
    let some E := parseStrictNat parts[2]! | throw "invalid E"
    if m == 0 || E == 0 then throw "vacuous DUAL_STABLE dimensions (m=0 or E=0)"
    let expected := 5 + E + m * E + m + E
    if parts.size != expected then throw s!"DUAL_STABLE token count mismatch: got {parts.size}, expected {expected}"
    let some ex := parseQ parts[3]! | throw "invalid ex"
    let some delta := parseQ parts[4]! | throw "invalid delta"
    let mut off := 5
    let some cxArr := parseQArray parts off E | throw "invalid cx"
    off := off + E
    let some cArr := parseQArray parts off (m * E) | throw "invalid c"
    off := off + m * E
    let some enArr := parseQArray parts off m | throw "invalid en"
    off := off + m
    let some muArr := parseQArray parts off E | throw "invalid mu"
    if h1 : cxArr.size = E then
      if h2 : cArr.size = m * E then
        if h3 : enArr.size = m then
          if h4 : muArr.size = E then
            let cMat := matOfArray cArr h2
            let cxVec := vecOfArray cxArr h1
            return checkNormalizedComps cMat cxVec &&
              checkDualStable cMat cxVec (vecOfArray enArr h3) ex delta (vecOfArray muArr h4)
          else throw "size mismatch mu"
        else throw "size mismatch en"
      else throw "size mismatch c"
    else throw "size mismatch cx"
  | "PRIMAL_UNSTABLE" =>
    if parts.size < 4 then throw "truncated PRIMAL_UNSTABLE header"
    let some m := parseStrictNat parts[1]! | throw "invalid m"
    let some E := parseStrictNat parts[2]! | throw "invalid E"
    if m == 0 || E == 0 then throw "vacuous PRIMAL_UNSTABLE dimensions (m=0 or E=0)"
    let expected := 4 + E + m * E + m + m
    if parts.size != expected then throw s!"PRIMAL_UNSTABLE token count mismatch: got {parts.size}, expected {expected}"
    let some ex := parseQ parts[3]! | throw "invalid ex"
    let mut off := 4
    let some cxArr := parseQArray parts off E | throw "invalid cx"
    off := off + E
    let some cArr := parseQArray parts off (m * E) | throw "invalid c"
    off := off + m * E
    let some enArr := parseQArray parts off m | throw "invalid en"
    off := off + m
    let some lamArr := parseQArray parts off m | throw "invalid lam"
    if h1 : cxArr.size = E then
      if h2 : cArr.size = m * E then
        if h3 : enArr.size = m then
          if h4 : lamArr.size = m then
            let cMat := matOfArray cArr h2
            let cxVec := vecOfArray cxArr h1
            return checkNormalizedComps cMat cxVec &&
              checkPrimalUnstable cMat cxVec (vecOfArray enArr h3) ex (vecOfArray lamArr h4)
          else throw "size mismatch lam"
        else throw "size mismatch en"
      else throw "size mismatch c"
    else throw "size mismatch cx"
  | "INTERVAL_STABLE" =>
    if parts.size < 7 then throw "truncated INTERVAL_STABLE header"
    let some m := parseStrictNat parts[1]! | throw "invalid m"
    let some E := parseStrictNat parts[2]! | throw "invalid E"
    if m == 0 || E == 0 then throw "vacuous INTERVAL_STABLE dimensions (m=0 or E=0)"
    let expected := 7 + E + m * E + m + m + E
    if parts.size != expected then throw s!"INTERVAL_STABLE token count mismatch: got {parts.size}, expected {expected}"
    let some ex := parseQ parts[3]! | throw "invalid ex"
    let some wx := parseQ parts[4]! | throw "invalid wx"
    let some eps := parseQ parts[5]! | throw "invalid eps"
    let some delta := parseQ parts[6]! | throw "invalid delta"
    let mut off := 7
    let some cxArr := parseQArray parts off E | throw "invalid cx"
    off := off + E
    let some cArr := parseQArray parts off (m * E) | throw "invalid c"
    off := off + m * E
    let some enArr := parseQArray parts off m | throw "invalid en"
    off := off + m
    let some wArr := parseQArray parts off m | throw "invalid w"
    off := off + m
    let some muArr := parseQArray parts off E | throw "invalid mu"
    if h1 : cxArr.size = E then
      if h2 : cArr.size = m * E then
        if h3 : enArr.size = m then
          if h4 : wArr.size = m then
            if h5 : muArr.size = E then
              return checkIntervalStableFromNominal
                (matOfArray cArr h2) (vecOfArray cxArr h1)
                (vecOfArray enArr h3) ex (vecOfArray wArr h4) wx eps delta (vecOfArray muArr h5)
            else throw "size mismatch mu"
          else throw "size mismatch w"
        else throw "size mismatch en"
      else throw "size mismatch c"
    else throw "size mismatch cx"
  | "INTERVAL_UNSTABLE" =>
    if parts.size < 6 then throw "truncated INTERVAL_UNSTABLE header"
    let some m := parseStrictNat parts[1]! | throw "invalid m"
    let some E := parseStrictNat parts[2]! | throw "invalid E"
    if m == 0 || E == 0 then throw "vacuous INTERVAL_UNSTABLE dimensions (m=0 or E=0)"
    let expected := 6 + E + m * E + m + m + m
    if parts.size != expected then throw s!"INTERVAL_UNSTABLE token count mismatch: got {parts.size}, expected {expected}"
    let some ex := parseQ parts[3]! | throw "invalid ex"
    let some wx := parseQ parts[4]! | throw "invalid wx"
    let some eps := parseQ parts[5]! | throw "invalid eps"
    let mut off := 6
    let some cxArr := parseQArray parts off E | throw "invalid cx"
    off := off + E
    let some cArr := parseQArray parts off (m * E) | throw "invalid c"
    off := off + m * E
    let some enArr := parseQArray parts off m | throw "invalid en"
    off := off + m
    let some wArr := parseQArray parts off m | throw "invalid w"
    off := off + m
    let some lamArr := parseQArray parts off m | throw "invalid lam"
    if h1 : cxArr.size = E then
      if h2 : cArr.size = m * E then
        if h3 : enArr.size = m then
          if h4 : wArr.size = m then
            if h5 : lamArr.size = m then
              return checkIntervalUnstableFromNominal
                (matOfArray cArr h2) (vecOfArray cxArr h1)
                (vecOfArray enArr h3) ex (vecOfArray wArr h4) wx eps (vecOfArray lamArr h5)
            else throw "size mismatch lam"
          else throw "size mismatch w"
        else throw "size mismatch en"
      else throw "size mismatch c"
    else throw "size mismatch cx"
  | "INTERVAL_FRAGILE_DESTAB" =>
    if parts.size < 6 then throw "truncated INTERVAL_FRAGILE_DESTAB header"
    let some m := parseStrictNat parts[1]! | throw "invalid m"
    let some E := parseStrictNat parts[2]! | throw "invalid E"
    if m == 0 || E == 0 then throw "vacuous INTERVAL_FRAGILE_DESTAB dimensions (m=0 or E=0)"
    let expected := 6 + E + m * E + m + m + m
    if parts.size != expected then throw s!"INTERVAL_FRAGILE_DESTAB token count mismatch: got {parts.size}, expected {expected}"
    let some ex := parseQ parts[3]! | throw "invalid ex"
    let some wx := parseQ parts[4]! | throw "invalid wx"
    let some eps := parseQ parts[5]! | throw "invalid eps"
    let mut off := 6
    let some cxArr := parseQArray parts off E | throw "invalid cx"
    off := off + E
    let some cArr := parseQArray parts off (m * E) | throw "invalid c"
    off := off + m * E
    let some enArr := parseQArray parts off m | throw "invalid en"
    off := off + m
    let some wArr := parseQArray parts off m | throw "invalid w"
    off := off + m
    let some lamArr := parseQArray parts off m | throw "invalid lam"
    if h1 : cxArr.size = E then
      if h2 : cArr.size = m * E then
        if h3 : enArr.size = m then
          if h4 : wArr.size = m then
            if h5 : lamArr.size = m then
              return checkIntervalFragileDestabFromNominal
                (matOfArray cArr h2) (vecOfArray cxArr h1)
                (vecOfArray enArr h3) ex (vecOfArray wArr h4) wx eps (vecOfArray lamArr h5)
            else throw "size mismatch lam"
          else throw "size mismatch w"
        else throw "size mismatch en"
      else throw "size mismatch c"
    else throw "size mismatch cx"
  | "INTERVAL_FRAGILE_STAB" =>
    if parts.size < 6 then throw "truncated INTERVAL_FRAGILE_STAB header"
    let some m := parseStrictNat parts[1]! | throw "invalid m"
    let some E := parseStrictNat parts[2]! | throw "invalid E"
    if m == 0 || E == 0 then throw "vacuous INTERVAL_FRAGILE_STAB dimensions (m=0 or E=0)"
    let expected := 6 + E + m * E + m + m + E
    if parts.size != expected then throw s!"INTERVAL_FRAGILE_STAB token count mismatch: got {parts.size}, expected {expected}"
    let some ex := parseQ parts[3]! | throw "invalid ex"
    let some wx := parseQ parts[4]! | throw "invalid wx"
    let some eps := parseQ parts[5]! | throw "invalid eps"
    let mut off := 6
    let some cxArr := parseQArray parts off E | throw "invalid cx"
    off := off + E
    let some cArr := parseQArray parts off (m * E) | throw "invalid c"
    off := off + m * E
    let some enArr := parseQArray parts off m | throw "invalid en"
    off := off + m
    let some wArr := parseQArray parts off m | throw "invalid w"
    off := off + m
    let some muArr := parseQArray parts off E | throw "invalid mu"
    if h1 : cxArr.size = E then
      if h2 : cArr.size = m * E then
        if h3 : enArr.size = m then
          if h4 : wArr.size = m then
            if h5 : muArr.size = E then
              return checkIntervalFragileStabFromNominal
                (matOfArray cArr h2) (vecOfArray cxArr h1)
                (vecOfArray enArr h3) ex (vecOfArray wArr h4) wx eps (vecOfArray muArr h5)
            else throw "size mismatch mu"
          else throw "size mismatch w"
        else throw "size mismatch en"
      else throw "size mismatch c"
    else throw "size mismatch cx"
  | "BORN_LDLT" =>
    let some n := parseStrictNat parts[1]! | throw "invalid n"
    if n == 0 then throw "vacuous BORN_LDLT dimension (n=0)"
    let expected := 2 + n * n + n * n + n
    if parts.size != expected then throw s!"BORN_LDLT token count mismatch: got {parts.size}, expected {expected}"
    let mut off := 2
    let some cArr := parseQArray parts off (n * n) | throw "invalid C"
    off := off + n * n
    let some lArr := parseQArray parts off (n * n) | throw "invalid L"
    off := off + n * n
    let some dArr := parseQArray parts off n | throw "invalid d"
    if h1 : cArr.size = n * n then
      if h2 : lArr.size = n * n then
        if h3 : dArr.size = n then
          return checkBornLDLT (matOfArray cArr h1) (matOfArray lArr h2) (vecOfArray dArr h3)
        else throw "size mismatch d"
      else throw "size mismatch L"
    else throw "size mismatch C"
  | "BORN_NON_PD" =>
    let some n := parseStrictNat parts[1]! | throw "invalid n"
    if n == 0 then throw "vacuous BORN_NON_PD dimension (n=0)"
    let expected := 2 + n * n + n
    if parts.size != expected then throw s!"BORN_NON_PD token count mismatch: got {parts.size}, expected {expected}"
    let mut off := 2
    let some cArr := parseQArray parts off (n * n) | throw "invalid C"
    off := off + n * n
    let some vArr := parseQArray parts off n | throw "invalid v"
    if h1 : cArr.size = n * n then
      if h2 : vArr.size = n then
        return checkBornNonPD (matOfArray cArr h1) (vecOfArray vArr h2)
      else throw "size mismatch v"
    else throw "size mismatch C"
  | "WEYL_ROBUST" =>
    if parts.size < 4 then throw "truncated WEYL_ROBUST header"
    let some n := parseStrictNat parts[1]! | throw "invalid n"
    if n == 0 then throw "vacuous WEYL_ROBUST dimension (n=0)"
    let expected := 4 + n * n + n * n + n
    if parts.size != expected then throw s!"WEYL_ROBUST token count mismatch: got {parts.size}, expected {expected}"
    let some lam0 := parseQ parts[2]! | throw "invalid lam0"
    let some delta := parseQ parts[3]! | throw "invalid delta"
    let mut off := 4
    let some cArr := parseQArray parts off (n * n) | throw "invalid C"
    off := off + n * n
    let some lArr := parseQArray parts off (n * n) | throw "invalid L"
    off := off + n * n
    let some dArr := parseQArray parts off n | throw "invalid d"
    if h1 : cArr.size = n * n then
      if h2 : lArr.size = n * n then
        if h3 : dArr.size = n then
          return checkWeylRobustBorn
            (matOfArray cArr h1) (matOfArray lArr h2) (vecOfArray dArr h3) lam0 delta
        else throw "size mismatch d"
      else throw "size mismatch L"
    else throw "size mismatch C"
  | "WEYL_FRAGILE" =>
    if parts.size < 3 then throw "truncated WEYL_FRAGILE header"
    let some n := parseStrictNat parts[1]! | throw "invalid n"
    if n == 0 then throw "vacuous WEYL_FRAGILE dimension (n=0)"
    let expected := 3 + n * n + n
    if parts.size != expected then throw s!"WEYL_FRAGILE token count mismatch: got {parts.size}, expected {expected}"
    let some delta := parseQ parts[2]! | throw "invalid delta"
    let mut off := 3
    let some cArr := parseQArray parts off (n * n) | throw "invalid C"
    off := off + n * n
    let some vArr := parseQArray parts off n | throw "invalid v"
    if h1 : cArr.size = n * n then
      if h2 : vArr.size = n then
        return checkWeylFragile (matOfArray cArr h1) delta (vecOfArray vArr h2)
      else throw "size mismatch v"
    else throw "size mismatch C"
  | "MANDEL_WEYL_ROBUST" =>
    if parts.size < 3 then throw "truncated MANDEL_WEYL_ROBUST header"
    let expected := 3 + 36 + 36 + 6
    if parts.size != expected then throw s!"MANDEL_WEYL_ROBUST token count mismatch: got {parts.size}, expected {expected}"
    let some lam0 := parseQ parts[1]! | throw "invalid lam0"
    let some delta := parseQ parts[2]! | throw "invalid delta"
    let mut off := 3
    let some cArr := parseQArray parts off 36 | throw "invalid C"
    off := off + 36
    let some lArr := parseQArray parts off 36 | throw "invalid L"
    off := off + 36
    let some dArr := parseQArray parts off 6 | throw "invalid d"
    if h1 : cArr.size = 6 * 6 then
      if h2 : lArr.size = 6 * 6 then
        if h3 : dArr.size = 6 then
          return checkMandelWeylRobustBorn
            (matOfArray cArr h1) (matOfArray lArr h2) (vecOfArray dArr h3) lam0 delta
        else throw "size mismatch d"
      else throw "size mismatch L"
    else throw "size mismatch C"
  | "MANDEL_WEYL_FRAGILE" =>
    if parts.size < 2 then throw "truncated MANDEL_WEYL_FRAGILE header"
    let expected := 2 + 36 + 6
    if parts.size != expected then throw s!"MANDEL_WEYL_FRAGILE token count mismatch: got {parts.size}, expected {expected}"
    let some delta := parseQ parts[1]! | throw "invalid delta"
    let mut off := 2
    let some cArr := parseQArray parts off 36 | throw "invalid C"
    off := off + 36
    let some vArr := parseQArray parts off 6 | throw "invalid v"
    if h1 : cArr.size = 6 * 6 then
      if h2 : vArr.size = 6 then
        return checkMandelWeylFragile (matOfArray cArr h1) delta (vecOfArray vArr h2)
      else throw "size mismatch v"
    else throw "size mismatch C"
  | _ => throw s!"unknown certificate kind: {kind}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let content ← IO.FS.readFile path
    let lines := content.splitOn "\n"
    let mut total := 0
    let mut passed := 0
    let mut failed := 0
    for line in lines do
      let t := line.trim
      if t.isEmpty || t.startsWith "#" then
        continue
      total := total + 1
      match verifyLine t with
      | .ok true => passed := passed + 1
      | .ok false =>
        failed := failed + 1
        IO.eprintln s!"[FAIL] line {total}: certificate rejected"
      | .error err =>
        failed := failed + 1
        IO.eprintln s!"[ERR] line {total}: {err}"
    IO.println s!"certmat-check: total={total} passed={passed} failed={failed}"
    return if failed == 0 && total > 0 then 0 else 1
  | _ =>
    IO.eprintln "Usage: certmat-check <certificates.tsv>"
    return 2
