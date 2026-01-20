Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Lists.Permutation.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.
Open Scope string_scope.

Definition space : ascii := " "%char.
Definition space_str : string := String space EmptyString.

Fixpoint to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: to_list s'
  end.

Definition NoSpace (s : string) : Prop :=
  Forall (fun c => c <> space) (to_list s).

Definition ascii_le (a b : ascii) : Prop :=
  nat_of_ascii a <= nat_of_ascii b.

Inductive join_with_space : list string -> string -> Prop :=
| join_nil : join_with_space [] EmptyString
| join_one : forall w, join_with_space [w] w
| join_more : forall w1 w2 ws rest,
    join_with_space (w2 :: ws) rest ->
    join_with_space (w1 :: w2 :: ws) (w1 ++ space_str ++ rest).

Definition split_by_space (s : string) (ws : list string) : Prop :=
  join_with_space ws s /\ Forall NoSpace ws.

Definition word_sort_spec (w : string) (w' : string) : Prop :=
  Permutation (to_list w) (to_list w') /\ Sorted ascii_le (to_list w').

Definition anti_shuffle_spec (s : string) (res : string) : Prop :=
  exists ws ws',
    split_by_space s ws /\
    Forall2 word_sort_spec ws ws' /\
    join_with_space ws' res.