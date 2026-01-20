Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

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

Definition in_range (lo hi n : nat) : bool :=
  andb (Nat.leb lo n) (Nat.leb n hi).

Definition greek_upper_second (n : nat) : bool := in_range 145 170 n.
Definition greek_lower_second (n : nat) : bool := in_range 177 190 n.

Fixpoint has_letter (s : string) : bool :=
  match s with
  | EmptyString => false
  | String b1 s' =>
      if is_alpha b1 then true
      else match s' with
           | EmptyString => false
           | String b2 s'' =>
               if Nat.eqb (ascii_code b1) 206
               then orb (greek_upper_second (ascii_code b2)) (greek_lower_second (ascii_code b2))
               else has_letter s'
           end
  end.

Fixpoint string_rev_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => string_rev_aux s' (String c acc)
  end.

Definition string_rev (s : string) : string := string_rev_aux s EmptyString.

Fixpoint swapcase_utf8 (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String b1 s' =>
      let n1 := ascii_code b1 in
      if is_lower b1 then String (ascii_of_nat (n1 - 32)) (swapcase_utf8 s')
      else if is_upper b1 then String (ascii_of_nat (n1 + 32)) (swapcase_utf8 s')
      else match s' with
           | EmptyString => String b1 EmptyString
           | String b2 s'' =>
               let n2 := ascii_code b2 in
               if Nat.eqb n1 206 then
                 if greek_lower_second n2 then
                   String b1 (String (ascii_of_nat (n2 - 32)) (swapcase_utf8 s''))
                 else if greek_upper_second n2 then
                   String b1 (String (ascii_of_nat (n2 + 32)) (swapcase_utf8 s''))
                 else String b1 (swapcase_utf8 s')
               else String b1 (swapcase_utf8 s')
           end
  end.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = swapcase_utf8 s
  else r = string_rev s.

Example solve_spec_unicode : solve_spec ("अমΑβγΔমβুমল"%string) ("अমαΒΓδমΒুমল"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.