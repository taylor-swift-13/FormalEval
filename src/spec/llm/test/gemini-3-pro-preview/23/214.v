Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Fixpoint codes_to_string (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: ns => String (ascii_of_nat n) (codes_to_string ns)
  end.

Definition input_str : string := codes_to_string [
  224; 232; 236; 242; 249;
  225; 233; 237; 243; 250; 253;
  226; 234; 238; 232; 244; 251;
  227; 241; 245;
  228; 235; 239; 246; 252; 255;
  231
].

Example test_strlen_unicode : strlen_spec input_str 27.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.