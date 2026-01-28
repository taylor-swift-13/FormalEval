Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition problem_62_spec (xs ys : list Z) : Prop :=
  length ys = Nat.sub (length xs) 1 /\
  forall (i : nat),
    (i < length ys)%nat ->
    nth i ys 0 = (Z.of_nat (i + 1)) * (nth (i + 1) xs 0).

(* Corrected derivative function *)
Fixpoint derivative (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | _ :: tl =>
      let fix aux (l : list Z) (n : nat) : list Z :=
          match l with
          | [] => []
          | a :: rest => (Z.of_nat n * a) :: aux rest (S n)
          end
      in aux tl 1
  end.

Example derivative_test :
  problem_62_spec
    [3%Z; 1%Z; 2%Z; 4%Z; 5%Z]
    [1%Z; 4%Z; 12%Z; 20%Z].
Proof.
  unfold problem_62_spec.
  split.
  - simpl. reflexivity.
  - intros i Hlt.
    simpl.
    revert i Hlt.
    unfold derivative.
    simpl.
    (* generalize aux and prove by induction on tl *)
    remember [1%Z; 2%Z; 4%Z; 5%Z] as tl eqn:Etl.
    revert Heqtl.
    induction tl as [|a rest IH]; intros tl_eq i Hlt; simpl in *.
    + lia.
    + inversion tl_eq; subst.
      destruct i as [|i'].
      * simpl. reflexivity.
      * simpl.
        rewrite IH with (i := i') by lia.
        reflexivity.
Qed.