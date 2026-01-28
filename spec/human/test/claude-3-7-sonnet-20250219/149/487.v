Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
Import ListNotations.

Open Scope string_scope.

Fixpoint lex_le (s1 s2 : string) : bool :=
  match s1,s2 with
  | EmptyString, _ => true
  | String _ _, EmptyString => false
  | String c1 t1, String c2 t2 =>
    match Ascii.compare c1 c2 with
    | Lt => true | Gt => false | Eq => lex_le t1 t2
    end
  end.

Definition string_le (s1 s2 : string) : bool :=
  match Nat.compare (length s1) (length s2) with
  | Lt => true | Gt => false | Eq => lex_le s1 s2
  end.

Definition has_even_length (s : string) : bool := Nat.even (length s).

Fixpoint insert_by (le : string -> string -> bool) (x : string) (l:list string) : list string :=
  match l with []=>[x] | h::t => if le x h then x::l else h::insert_by le x t end.

Fixpoint sort_by (le : string -> string -> bool) (l:list string) : list string :=
  match l with []=>[] | h::t => insert_by le h (sort_by le t) end.

Definition list_sort_impl (lst_in : list string) : list string :=
  sort_by string_le (filter has_even_length lst_in).

Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  output = list_sort_impl input.

Example test_case_149 :
  problem_149_spec ["abcd"; "mworldno"; "efg"; "ccccc"; "aklmncccccobcd"; "jkl"; "mno"; "mno"] ["abcd"; "mworldno"; "aklmncccccobcd"].
Proof.
  unfold problem_149_spec, list_sort_impl.
  simpl.
  (* Filter by has_even_length: *)
  (* "abcd" length 4 even -> keep *)
  (* "mworldno" length 8 even -> keep *)
  (* "efg" length 3 odd -> discard *)
  (* "ccccc" length 5 odd -> discard *)
  (* "aklmncccccobcd" length 13 odd -> double check *)
  (* Wait length "aklmncccccobcd" *)
  (* Count letters: a k l m n c c c c c o b c d *)
  (* length = 14? Let's count carefully: a(1) k(2) l(3) m(4) n(5) c(6) c(7) c(8) c(9) c(10) o(11) b(12) c(13) d(14) *)
  (* length = 14 even -> keep *)
  (* "jkl" length 3 odd -> discard *)
  (* "mno" length 3 odd -> discard *)
  (* "mno" length 3 odd -> discard *)
  (* So filter yields ["abcd"; "mworldno"; "aklmncccccobcd"] *)

  (* Sorting by string_le on these: *)
  (* lengths: abcd(4), mworldno(8), aklmncccccobcd(14) *)
  (* Length order is enough: 4 < 8 < 14 *)
  (* So sorted output is as given *)

  reflexivity.
Qed.