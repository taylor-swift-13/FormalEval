Require Import Coq.Reals.Reals.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Local Open Scope R_scope.

Definition ReqBool (x y : R) : bool :=
  if Req_EM_T x y then true else false.

Definition right_angle_triangle_spec (a b c : R) (res : bool) : Prop :=
  res =
    orb
      (orb (ReqBool (a * a + b * b) (c * c))
           (ReqBool (a * a + c * c) (b * b)))
      (ReqBool (b * b + c * c) (a * a)).

Example right_angle_triangle_spec_24_71115668501026_93_15108572417166_93_65019636949225 :
  right_angle_triangle_spec 24.71115668501026%R 93.15108572417166%R 93.65019636949225%R false.
Proof.
  unfold right_angle_triangle_spec.
  unfold ReqBool.
  destruct (Req_EM_T (24.71115668501026 * 24.71115668501026 + 93.15108572417166 * 93.15108572417166)
                     (93.65019636949225 * 93.65019636949225)) as [H1|H1].
  - exfalso.
    assert ((93.65019636949225 * 93.65019636949225) <
            (24.71115668501026 * 24.71115668501026 + 93.15108572417166 * 93.15108572417166)) by nra.
    rewrite <- H1 in H.
    now apply (Rlt_irrefl _) in H.
  - simpl.
    destruct (Req_EM_T (24.71115668501026 * 24.71115668501026 + 93.65019636949225 * 93.65019636949225)
                       (93.15108572417166 * 93.15108572417166)) as [H2|H2].
    + exfalso.
      assert ((93.15108572417166 * 93.15108572417166) <
              (24.71115668501026 * 24.71115668501026 + 93.65019636949225 * 93.65019636949225)) by nra.
      rewrite <- H2 in H.
      now apply (Rlt_irrefl _) in H.
    + simpl.
      destruct (Req_EM_T (93.15108572417166 * 93.15108572417166 + 93.65019636949225 * 93.65019636949225)
                         (24.71115668501026 * 24.71115668501026)) as [H3|H3].
      * exfalso.
        assert ((24.71115668501026 * 24.71115668501026) <
                (93.15108572417166 * 93.15108572417166 + 93.65019636949225 * 93.65019636949225)) by nra.
        rewrite <- H3 in H.
        now apply (Rlt_irrefl _) in H.
      * simpl.
        reflexivity.
Qed.