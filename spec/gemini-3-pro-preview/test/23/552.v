Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["  Tish!     sThe Quick Brown Fox Jumps Over The Lazy DogttTcricQukickn      4!n \n\n  1s  "], output = 88 *)
Example test_strlen_case : strlen_spec "  Tish!     sThe Quick Brown Fox Jumps Over The Lazy DogttTcricQukickn      4!n 

  1s  " 88.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.