Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Definition ascii_code (c : ascii) : nat := nat_of_ascii c.

Definition is_upper (c : ascii) : bool :=
  let n := ascii_code c in
  orb (andb (Nat.leb 65 n) (Nat.leb n 90))
      (orb (Nat.eqb n 145)
           (orb (Nat.eqb n 146)
                (orb (Nat.eqb n 147)
                     (Nat.eqb n 148)))).

Definition is_lower (c : ascii) : bool :=
  let n := ascii_code c in
  orb (andb (Nat.leb 97 n) (Nat.leb n 122))
      (orb (Nat.eqb n 177)
           (orb (Nat.eqb n 178)
                (orb (Nat.eqb n 179)
                     (Nat.eqb n 180)))).

Definition is_alpha (c : ascii) : bool := orb (is_upper c) (is_lower c).

Definition swapcase_char (c : ascii) : ascii :=
  let n := ascii_code c in
  if is_lower c then
    if andb (Nat.leb 97 n) (Nat.leb n 122)
    then ascii_of_nat (n - 32)
    else match n with
         | 177 => ascii_of_nat 145
         | 178 => ascii_of_nat 146
         | 179 => ascii_of_nat 147
         | 180 => ascii_of_nat 148
         | _ => c
         end
  else if is_upper c then
    if andb (Nat.leb 65 n) (Nat.leb n 90)
    then ascii_of_nat (n + 32)
    else match n with
         | 145 => ascii_of_nat 177
         | 146 => ascii_of_nat 178
         | 147 => ascii_of_nat 179
         | 148 => ascii_of_nat 180
         | _ => c
         end
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

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = string_map swapcase_char s
  else r = string_rev s.

Example solve_spec_Greek : solve_spec ("ΑβγΔ"%string) ("αΒΓδ"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.