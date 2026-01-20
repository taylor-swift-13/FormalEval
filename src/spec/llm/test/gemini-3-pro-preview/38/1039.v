Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Fixpoint list_to_string (l : list ascii) : string :=
  match l with
  | [] => EmptyString
  | c :: l' => String c (list_to_string l')
  end.

Fixpoint encode_cyclic_list (l : list ascii) : list ascii :=
  match l with
  | c1 :: c2 :: c3 :: rest => c2 :: c3 :: c1 :: (encode_cyclic_list rest)
  | _ => l
  end.

Definition encode_cyclic_spec (s : string) (res : string) : Prop :=
  res = list_to_string (encode_cyclic_list (string_to_list s)).

Fixpoint decode_cyclic_list (l : list ascii) : list ascii :=
  match l with
  | c1 :: c2 :: c3 :: rest => c3 :: c1 :: c2 :: (decode_cyclic_list rest)
  | _ => l
  end.

Definition decode_cyclic_spec (s : string) (res : string) : Prop :=
  res = list_to_string (decode_cyclic_list (string_to_list s)).

(* 
   Test case analysis:
   Input: "adabcdefj51214%^&&*876tylfrmlskyooifnmwddodffrrehfyj^%*^&yt3456ghijabc"
   Output: "aaddbcjef251%14&^&7*8y6trlfsmlokyfoiwnmoddfdferryhf%j^&*^3yt645ighbjac"
   
   Checking the logic:
   Input chunk "ada" -> Output chunk "aad"
   This corresponds to the transformation: c1::c2::c3 -> c3::c1::c2
   This matches the logic of decode_cyclic_list.
*)

Example test_case_proof : decode_cyclic_spec "adabcdefj51214%^&&*876tylfrmlskyooifnmwddodffrrehfyj^%*^&yt3456ghijabc" "aaddbcjef251%14&^&7*8y6trlfsmlokyfoiwnmoddfdferryhf%j^&*^3yt645ighbjac".
Proof.
  unfold decode_cyclic_spec.
  simpl.
  reflexivity.
Qed.