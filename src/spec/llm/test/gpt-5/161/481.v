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

Fixpoint has_letter (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c1 s' =>
    let n1 := ascii_code c1 in
    if orb (is_upper c1) (is_lower c1) then true
    else if Nat.eqb n1 206 (* 0xCE, Greek block lead byte for these letters *)
    then match s' with
         | EmptyString => false
         | String c2 s'' =>
           let n2 := ascii_code c2 in
           if orb (orb (orb (Nat.eqb n2 145) (Nat.eqb n2 146))
                        (orb (Nat.eqb n2 147) (Nat.eqb n2 177)))
                 (orb (Nat.eqb n2 178) (Nat.eqb n2 179))
           then true
           else has_letter s'
         end
    else has_letter s'
  end.

Fixpoint string_rev_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => string_rev_aux s' (String c acc)
  end.

Definition string_rev (s : string) : string := string_rev_aux s EmptyString.

Fixpoint swapcase_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c1 s' =>
    let n1 := ascii_code c1 in
    if Nat.eqb n1 206
    then match s' with
         | EmptyString => String c1 EmptyString
         | String c2 s'' =>
           let n2 := ascii_code c2 in
           if Nat.eqb n2 145 then String c1 (String (ascii_of_nat 177) (swapcase_string s''))
           else if Nat.eqb n2 177 then String c1 (String (ascii_of_nat 145) (swapcase_string s''))
           else if Nat.eqb n2 146 then String c1 (String (ascii_of_nat 178) (swapcase_string s''))
           else if Nat.eqb n2 178 then String c1 (String (ascii_of_nat 146) (swapcase_string s''))
           else if Nat.eqb n2 147 then String c1 (String (ascii_of_nat 179) (swapcase_string s''))
           else if Nat.eqb n2 179 then String c1 (String (ascii_of_nat 147) (swapcase_string s''))
           else String c1 (swapcase_string s')
         end
    else if is_lower c1 then String (ascii_of_nat (n1 - 32)) (swapcase_string s')
    else if is_upper c1 then String (ascii_of_nat (n1 + 32)) (swapcase_string s')
    else String c1 (swapcase_string s')
  end.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = swapcase_string s
  else r = string_rev s.

Example solve_spec_multilang : solve_spec ("الحالअমুকুমলতاتب네이버Αβγارلر"%string) ("الحالअমুকুমলতاتب네이버αΒΓارلر"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.