(* Import Coq's libraries for Rational Numbers and Integers *)
Require Import QArith ZArith Lia.

Open Scope Q_scope.
Open Scope Z_scope.

(* Definition of the specification for the problem *)
Definition problem_92_spec (x y z : Q) (b : bool) : Prop :=
  b = true <->
    (exists zx zy zz : Z,
      x = (zx # 1) /\
      y = (zy # 1) /\
      z = (zz # 1) /\
      (zx = zy + zz \/
       zy = zx + zz \/
       zz = zx + zy)).

(* Definition of the function any_int *)
Definition any_int (x y z : Q) : bool :=
  if (Z.eqb (Z_of_nat (Pos.to_nat (Qden x))) 1 &&
      Z.eqb (Z_of_nat (Pos.to_nat (Qden y))) 1 &&
      Z.eqb (Z_of_nat (Pos.to_nat (Qden z))) 1)%bool then
    let nx := Qnum x in
    let ny := Qnum y in
    let nz := Qnum z in
    (Z.eqb nx (ny + nz) || Z.eqb ny (nx + nz) || Z.eqb nz (nx + ny))%bool
  else
    false.

(* Example test case *)
Example test_any_int_1 : problem_92_spec (2#1) (3#1) (1#1) true.
Proof.
  unfold problem_92_spec.
  unfold any_int.
  split.
  - intros H.
    simpl in H.
    rewrite Z.eqb_refl in H.
    simpl in H.
    apply orb_true_iff in H.
    destruct H as [H | [H | H]];
    apply Z.eqb_eq in H;
    exists 2, 3, 1;
    split; [reflexivity|];
    split; [reflexivity|];
    split; [reflexivity|];
    auto.
  - intros [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    rewrite Hx, Hy, Hz.
    simpl.
    rewrite Z.eqb_refl.
    destruct Hsum as [H|[H|H]]; subst; simpl; try (rewrite Z.eqb_refl); reflexivity.
Qed.