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

Example test_case_proof : decode_cyclic_spec "Testing567The quick brown fox jumps over the lazy dog.0 123,Testing 123, testinTesting567The quick Testing567The quick brown fox jumps over the lazy dog.0 123,Testing 123, testing 123. testingabc 123.brown fox jumps over the lazy dog.0 123,Testing 123, testing 123. testingabc 123.g 123. testingabc 123." "sTenti6g5h7Tqe cuibk wrofn  oxmju pseovtr  hezlady .og10 ,23sTenti1g ,23e tistenTist5ngT67 heiqu cksTenti6g5h7Tqe cuibk wrofn  oxmju pseovtr  hezlady .og10 ,23sTenti1g ,23e tist ng312t. tesgincab2 1b3.wrofn  oxmju pseovtr  hezlady .og10 ,23sTenti1g ,23e tist ng312t. tesgincab2 1g3.2 1 3.stentibga1c .23".
Proof.
  unfold decode_cyclic_spec.
  simpl.
  reflexivity.
Qed.