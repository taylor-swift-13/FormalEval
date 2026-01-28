Require Import QArith ZArith.
Require Import Psatz.

Open Scope Q_scope.
Open Scope Z_scope.

(* 任意三个有理数输入均可，无附加约束 *)
Definition problem_92_pre (x y z : Q) : Prop := True.

(*
  any_int_spec is the program specification for the any_int function.
  It describes the relationship between the inputs x, y, z and the output b.
  - x, y, z : Q      Program inputs, using rational numbers to handle all cases.
  - b : bool         Program output, a boolean value.
*)
Definition problem_92_spec (x y z : Q) (b : bool) : Prop :=
  b = true <->
    (*
      The entire condition is expressed with an existential quantifier.
      This reads: "There exist integers zx, zy, and zz such that..."
    *)
    (exists zx zy zz : Z,
      (* Condition 1: ...x, y, and z are equal to those integers
         (represented as rationals). This is the correct way to assert
         that x, y, and z are all integers. *)
      x = (zx # 1) /\
      y = (zy # 1) /\
      z = (zz # 1) /\

      (* Condition 2: ...and those integers satisfy the summation property. *)
      (zx = zy + zz \/
       zy = zx + zz \/
       zz = zx + zy)).

Example test_problem_92 : problem_92_spec (-15 # 1) (20 # 1) (10 # 1) false.
Proof.
  unfold problem_92_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    destruct H as [zx [zy [zz [Hx [Hy [Hz Hsum]]]]]].
    injection Hx; intro Ezx.
    injection Hy; intro Ezy.
    injection Hz; intro Ezz.
    rewrite <- Ezx, <- Ezy, <- Ezz in Hsum.
    lia.
Qed.