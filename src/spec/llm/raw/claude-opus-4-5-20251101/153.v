
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

Definition is_uppercase (c : Ascii.ascii) : bool :=
  let n := Ascii.N_of_ascii c in
  andb (N.leb 65 n) (N.leb n 90).

Definition is_lowercase (c : Ascii.ascii) : bool :=
  let n := Ascii.N_of_ascii c in
  andb (N.leb 97 n) (N.leb n 122).

Fixpoint count_uppercase (s : string) : Z :=
  match s with
  | EmptyString => 0
  | String c rest => (if is_uppercase c then 1 else 0) + count_uppercase rest
  end.

Fixpoint count_lowercase (s : string) : Z :=
  match s with
  | EmptyString => 0
  | String c rest => (if is_lowercase c then 1 else 0) + count_lowercase rest
  end.

Definition strength (s : string) : Z :=
  count_uppercase s - count_lowercase s.

Fixpoint find_strongest (extensions : list string) (current_best : option string) (current_max : Z) : option string :=
  match extensions with
  | [] => current_best
  | e :: rest =>
    let s := strength e in
    match current_best with
    | None => find_strongest rest (Some e) s
    | Some _ =>
      if Z.ltb current_max s then
        find_strongest rest (Some e) s
      else
        find_strongest rest current_best current_max
    end
  end.

Definition strongest_extension (extensions : list string) : option string :=
  match extensions with
  | [] => None
  | e :: rest => find_strongest rest (Some e) (strength e)
  end.

Definition Strongest_Extension_spec (class_name : string) (extensions : list string) (result : string) : Prop :=
  extensions <> [] /\
  exists strongest : string,
    In strongest extensions /\
    (forall e : string, In e extensions -> strength e <= strength strongest) /\
    (forall e : string, In e extensions -> strength e = strength strongest ->
      exists l1 l2 l3 l4 : list string,
        extensions = l1 ++ [strongest] ++ l2 /\
        extensions = l3 ++ [e] ++ l4 /\
        length l1 <= length l3) /\
    result = (class_name ++ "." ++ strongest)%string.
