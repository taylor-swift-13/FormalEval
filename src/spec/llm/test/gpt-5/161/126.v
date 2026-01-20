Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

Definition ascii_code (c : ascii) : nat := nat_of_ascii c.

Definition is_upper (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 65 n) (Nat.leb n 90).

Definition is_lower (c : ascii) : bool :=
  let n := ascii_code c in andb (Nat.leb 97 n) (Nat.leb n 122).

Definition is_alpha (c : ascii) : bool := orb (is_upper c) (is_lower c).

Definition swapcase_char (c : ascii) : ascii :=
  let n := ascii_code c in
  if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else c.

Fixpoint string_map (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (string_map f s')
  end.

Fixpoint has_letter (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' => orb (is_alpha c) (has_letter s')
  end.

Fixpoint string_rev_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => string_rev_aux s' (String c acc)
  end.

Definition string_rev (s : string) : string := string_rev_aux s EmptyString.

Fixpoint list_ascii_to_string (l : list ascii) : string :=
  match l with
  | nil => EmptyString
  | cons c cs => String c (list_ascii_to_string cs)
  end.

Fixpoint string_append (s1 s2 : string) : string :=
  match s1 with
  | EmptyString => s2
  | String c s1' => String c (string_append s1' s2)
  end.

Fixpoint read_utf8_blocks (s : string) : list (list ascii) :=
  match s with
  | EmptyString => nil
  | String c1 s1 =>
      let n1 := ascii_code c1 in
      if Nat.eqb n1 240
      then match s1 with
           | String c2 s2 =>
             match s2 with
             | String c3 s3 =>
               match s3 with
               | String c4 s4 =>
                 cons (cons c1 (cons c2 (cons c3 (cons c4 nil)))) (read_utf8_blocks s4)
               | _ => cons (cons c1 nil) (read_utf8_blocks s1)
               end
             | _ => cons (cons c1 nil) (read_utf8_blocks s1)
             end
           | _ => cons (cons c1 nil) (read_utf8_blocks s1)
           end
      else cons (cons c1 nil) (read_utf8_blocks s1)
  end.

Fixpoint blocks_rev_to_string (blocks : list (list ascii)) : string :=
  match blocks with
  | nil => EmptyString
  | cons b bs => string_append (blocks_rev_to_string bs) (list_ascii_to_string b)
  end.

Definition string_rev_utf8 (s : string) : string :=
  blocks_rev_to_string (read_utf8_blocks s).

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = string_map swapcase_char s
  else r = string_rev_utf8 s.

Example solve_spec_emojis : solve_spec ("😎😎😀😂😎"%string) ("😎😂😀😎😎"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.