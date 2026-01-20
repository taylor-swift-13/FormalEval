Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition tab : ascii := Ascii.ascii_of_nat 9.

Definition two_tabs : string := String tab (String tab EmptyString).

Example strlen_spec_two_tabs: strlen_spec two_tabs 2.
Proof.
  unfold strlen_spec.
  unfold two_tabs, tab.
  simpl.
  reflexivity.
Qed.

Example strlen_test_two_tabs_Z: Z.of_nat (String.length two_tabs) = 2%Z.
Proof.
  unfold two_tabs, tab.
  simpl.
  reflexivity.
Qed.