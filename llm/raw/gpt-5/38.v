Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Open Scope string_scope.

Fixpoint concat_strings (ls : list string) : string :=
  match ls with
  | nil => EmptyString
  | x :: xs => x ++ concat_strings xs
  end.

Definition chunk3 (s : string) (groups : list string) : Prop :=
  s = concat_strings groups /\
  List.length groups = Nat.div (String.length s + 2) 3 /\
  List.Forall (fun g => String.length g <= 3) groups /\
  (groups = nil /\ s = EmptyString \/
   exists pre last,
     groups = pre ++ last :: nil /\
     List.Forall (fun g => String.length g = 3) pre /\
     String.length last <= 3).

Definition rot_left3 (g g' : string) : Prop :=
  (exists a b c,
      g = String a (String b (String c EmptyString)) /\
      g' = String b (String c (String a EmptyString)))
  \/ (String.length g <> 3 /\ g' = g).

Definition rot_right3 (g g' : string) : Prop :=
  (exists a b c,
      g = String a (String b (String c EmptyString)) /\
      g' = String c (String a (String b EmptyString)))
  \/ (String.length g <> 3 /\ g' = g).

Definition encode_cyclic_spec (s : string) (encoded : string) : Prop :=
  exists groups groups',
    chunk3 s groups /\
    List.Forall2 rot_left3 groups groups' /\
    encoded = concat_strings groups'.

Definition decode_cyclic_spec (s : string) (decoded : string) : Prop :=
  exists groups groups',
    chunk3 s groups /\
    List.Forall2 rot_right3 groups groups' /\
    decoded = concat_strings groups'.