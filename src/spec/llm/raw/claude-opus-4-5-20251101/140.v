
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

Fixpoint count_consecutive_spaces (s : list ascii) : nat :=
  match s with
  | nil => 0
  | c :: rest =>
    if Ascii.eqb c " "%char then
      1 + count_consecutive_spaces rest
    else
      0
  end.

Fixpoint replace_spaces_helper (s : list ascii) (in_long_space : bool) (space_count : nat) : list ascii :=
  match s with
  | nil =>
    if in_long_space then
      if Nat.leb 3 space_count then
        ["-"%char]
      else
        list_repeat " "%char space_count
    else
      nil
  | c :: rest =>
    if Ascii.eqb c " "%char then
      replace_spaces_helper rest true (space_count + 1)
    else
      if in_long_space then
        if Nat.leb 3 space_count then
          ["-"%char] ++ [c] ++ replace_spaces_helper rest false 0
        else
          (map (fun _ => "_"%char) (seq 0 space_count)) ++ [c] ++ replace_spaces_helper rest false 0
      else
        [c] ++ replace_spaces_helper rest false 0
  end
with list_repeat (c : ascii) (n : nat) : list ascii :=
  match n with
  | 0 => nil
  | S n' => c :: list_repeat c n'
  end.

Definition fix_spaces_spec (text : string) (result : string) : Prop :=
  forall i,
    (forall pos len,
      len >= 3 ->
      (forall j, j >= pos /\ j < pos + len -> 
        String.get j text = Some " "%char) ->
      exists pos' len',
        len' = 1 /\
        String.get pos' result = Some "-"%char) /\
    (forall pos,
      String.get pos text = Some " "%char ->
      (pos = 0 \/ String.get (pos - 1) text <> Some " "%char) ->
      (pos = String.length text - 1 \/ String.get (pos + 1) text <> Some " "%char) ->
      exists pos',
        String.get pos' result = Some "_"%char) /\
    (forall pos c,
      String.get pos text = Some c ->
      c <> " "%char ->
      exists pos',
        String.get pos' result = Some c).
