import Lake
open Lake DSL

-- CertMat Lean 4 형식 검증 커널 패키지 설정 (외부 Mathlib 의존성 없음)
package certmat where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib CertMat where
  roots := #[`CertMat]

lean_exe «certmat-check» where
  root := `Main
