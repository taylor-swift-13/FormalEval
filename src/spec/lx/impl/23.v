Require Import Coq.Strings.String.
Open Scope string_scope.

(* 实现：返回字符串长度 *)
Definition strlen_impl (s : string) : nat := String.length s.

Example strlen_impl_empty: strlen_impl "" = (0)%nat.
Proof. reflexivity. Qed.

Example strlen_impl_abc: strlen_impl "abc" = (3)%nat.
Proof. reflexivity. Qed.

Definition strlen_spec (s : string) (output : nat) : Prop :=
  output = strlen_impl s.


