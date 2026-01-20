Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Fixpoint factorial (n : nat) : Z :=
  match n with
  | O => 1
  | S n' => Z.of_nat n * factorial n'
  end.

Fixpoint sum_1_to_n (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => Z.of_nat n + sum_1_to_n n'
  end.

Definition f_element (i : nat) : Z :=
  if Nat.even i then factorial i
  else sum_1_to_n i.

Fixpoint f_list (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => f_list n' ++ [f_element n]
  end.

Definition f_spec (n : nat) (result : list Z) : Prop :=
  result = f_list n /\
  length result = n /\
  forall i : nat, (1 <= i <= n)%nat ->
    nth (i - 1) result 0 = f_element i.

Example f_test_case :
  f_spec 5%nat [1%Z; 2%Z; 6%Z; 24%Z; 15%Z].
Proof.
  unfold f_spec.
  split.
  - vm_compute. reflexivity.
  - split.
    + reflexivity.
    + intros i Hi.
      destruct Hi as [Hi1 Hi2].
      destruct i as [|i'].
      * exfalso. lia.
      * simpl.
        destruct i' as [|i''].
        { vm_compute. reflexivity. }
        destruct i'' as [|i'''].
        { vm_compute. reflexivity. }
        destruct i''' as [|i''''].
        { vm_compute. reflexivity. }
        destruct i'''' as [|i'''''].
        { vm_compute. reflexivity. }
        destruct i'''''.
        { vm_compute. reflexivity. }
        { exfalso. lia. }
Qed.