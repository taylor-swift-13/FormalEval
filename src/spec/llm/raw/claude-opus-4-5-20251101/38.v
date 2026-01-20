
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

Definition cycle_group (group : list ascii) : list ascii :=
  match group with
  | [a; b; c] => [b; c; a]
  | _ => group
  end.

Definition uncycle_group (group : list ascii) : list ascii :=
  match group with
  | [a; b; c] => [c; a; b]
  | _ => group
  end.

Fixpoint split_into_groups (l : list ascii) : list (list ascii) :=
  match l with
  | [] => []
  | [a] => [[a]]
  | [a; b] => [[a; b]]
  | a :: b :: c :: rest => [a; b; c] :: split_into_groups rest
  end.

Definition encode_cyclic_list (l : list ascii) : list ascii :=
  flat_map cycle_group (split_into_groups l).

Definition decode_cyclic_list (l : list ascii) : list ascii :=
  flat_map uncycle_group (split_into_groups l).

Definition string_to_list (s : string) : list ascii :=
  list_ascii_of_string s.

Definition list_to_string (l : list ascii) : string :=
  string_of_list_ascii l.

Definition encode_cyclic_spec (s : string) (encoded : string) : Prop :=
  encoded = list_to_string (encode_cyclic_list (string_to_list s)).

Definition decode_cyclic_spec (s : string) (decoded : string) : Prop :=
  decoded = list_to_string (decode_cyclic_list (string_to_list s)).

Definition decode_inverts_encode_spec (original : string) : Prop :=
  forall encoded decoded : string,
    encode_cyclic_spec original encoded ->
    decode_cyclic_spec encoded decoded ->
    decoded = original.
