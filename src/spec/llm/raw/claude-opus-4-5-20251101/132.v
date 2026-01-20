
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Open Scope Z_scope.

Definition char_eq (c1 c2 : Ascii.ascii) : bool :=
  Ascii.eqb c1 c2.

Definition open_bracket : Ascii.ascii := "["%char.
Definition close_bracket : Ascii.ascii := "]"%char.

Fixpoint string_to_list (s : string) : list Ascii.ascii :=
  match s with
  | EmptyString => nil
  | String c rest => c :: string_to_list rest
  end.

Definition is_open (c : Ascii.ascii) : bool := char_eq c open_bracket.
Definition is_close (c : Ascii.ascii) : bool := char_eq c close_bracket.

Fixpoint check_from_position (chars : list Ascii.ascii) (cnt : Z) (max_nest : Z) : bool :=
  match chars with
  | nil => false
  | c :: rest =>
    let new_cnt := if is_open c then cnt + 1 else cnt - 1 in
    let new_max := Z.max max_nest new_cnt in
    if new_cnt =? 0 then
      if new_max >=? 2 then true else false
    else
      check_from_position rest new_cnt new_max
  end.

Fixpoint is_nested_aux (chars : list Ascii.ascii) (full : list Ascii.ascii) : bool :=
  match chars with
  | nil => false
  | c :: rest =>
    if is_close c then
      is_nested_aux rest full
    else
      if check_from_position chars 0 0 then true
      else is_nested_aux rest full
  end.

Definition is_nested_impl (s : string) : bool :=
  let chars := string_to_list s in
  is_nested_aux chars chars.

Definition has_valid_nested_subsequence (s : string) : Prop :=
  exists i j k l : nat,
    i < j /\ j <= k /\ k < l /\
    l <= String.length s /\
    forall n, (n = i \/ n = j \/ n = k \/ n = l) ->
      match String.get n s with
      | Some c => (n = i \/ n = k) /\ is_open c = true \/
                  (n = j \/ n = l) /\ is_close c = true
      | None => False
      end.

Definition is_nested_spec (s : string) (result : bool) : Prop :=
  result = is_nested_impl s.
