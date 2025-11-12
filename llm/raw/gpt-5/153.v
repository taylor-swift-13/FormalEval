Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Open Scope string_scope.
Open Scope Z_scope.

Definition is_upper (a : ascii) : bool :=
  let n := nat_of_ascii a in
  Nat.leb (nat_of_ascii ("A"%char)) n && Nat.leb n (nat_of_ascii ("Z"%char)).

Definition is_lower (a : ascii) : bool :=
  let n := nat_of_ascii a in
  Nat.leb (nat_of_ascii ("a"%char)) n && Nat.leb n (nat_of_ascii ("z"%char)).

Fixpoint strength (s : string) : Z :=
  match s with
  | EmptyString => 0
  | String ch rest =>
      strength rest + (if is_upper ch then 1 else if is_lower ch then (-1) else 0)
  end.

Definition Strongest_Extension_spec
  (class_name : string) (extensions : list string) (res : string) : Prop :=
  exists e pre post,
    extensions = pre ++ e :: post /\
    res = class_name ++ "." ++ e /\
    (forall e', In e' extensions -> strength e' <= strength e) /\
    (forall e', In e' pre -> strength e' < strength e).