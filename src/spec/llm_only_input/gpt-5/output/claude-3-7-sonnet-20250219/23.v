Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example strlen_empty_ok :
  strlen_spec ""%string 0%nat.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_empty_output_Z :
  Z.of_nat (String.length ""%string) = 0%Z.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_case_singleton_empty_string_output :
  map (fun s => Z.of_nat (String.length s)) [""%string] = [0%Z].
Proof.
  simpl.
  reflexivity.
Qed.