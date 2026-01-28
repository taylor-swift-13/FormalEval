Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Fixpoint utf8_length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
      match c with
      | Ascii _ _ _ _ _ _ false true => utf8_length s'
      | _ => S (utf8_length s')
      end
  end.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = utf8_length s.

Example test_strlen_new : strlen_spec "           àèìòùáéíóúýâêîôiwTstgrsr1ngïöüÿç" 43.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.