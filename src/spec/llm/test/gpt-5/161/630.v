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

Fixpoint has_letter_aux (prev : ascii) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' =>
      let nprev := ascii_code prev in
      let n := ascii_code c in
      let uml_lower :=
        andb (Nat.eqb nprev 195)
             (orb (Nat.eqb n 164)
             (orb (Nat.eqb n 171)
             (orb (Nat.eqb n 175)
             (orb (Nat.eqb n 182)
                  (Nat.eqb n 188))))) in
      let uml_upper :=
        andb (Nat.eqb nprev 195)
             (orb (Nat.eqb n 132)
             (orb (Nat.eqb n 139)
             (orb (Nat.eqb n 143)
             (orb (Nat.eqb n 150)
                  (Nat.eqb n 156))))) in
      orb (orb (is_alpha c) uml_lower) (orb uml_upper (has_letter_aux c s'))
  end.

Definition has_letter (s : string) : bool := has_letter_aux (ascii_of_nat 0) s.

Fixpoint string_rev_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => string_rev_aux s' (String c acc)
  end.

Definition string_rev (s : string) : string := string_rev_aux s EmptyString.

Definition swapcase_char_utf8 (prev c : ascii) : ascii :=
  let n := ascii_code c in
  let nprev := ascii_code prev in
  let uml_lower :=
    andb (Nat.eqb nprev 195)
         (orb (Nat.eqb n 164)
         (orb (Nat.eqb n 171)
         (orb (Nat.eqb n 175)
         (orb (Nat.eqb n 182)
              (Nat.eqb n 188))))) in
  let uml_upper :=
    andb (Nat.eqb nprev 195)
         (orb (Nat.eqb n 132)
         (orb (Nat.eqb n 139)
         (orb (Nat.eqb n 143)
         (orb (Nat.eqb n 150)
              (Nat.eqb n 156))))) in
  if is_lower c then ascii_of_nat (n - 32)
  else if is_upper c then ascii_of_nat (n + 32)
  else if uml_lower then ascii_of_nat (n - 32)
  else if uml_upper then ascii_of_nat (n + 32)
  else c.

Fixpoint string_map_with_prev (f : ascii -> ascii -> ascii) (prev : ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f prev c) (string_map_with_prev f c s')
  end.

Definition string_swapcase_utf8 (s : string) : string :=
  string_map_with_prev swapcase_char_utf8 (ascii_of_nat 0) s.

Definition solve_spec (s : string) (r : string) : Prop :=
  if has_letter s
  then r = string_swapcase_utf8 s
  else r = string_rev s.

Example solve_spec_umlauts_korean : solve_spec ("äëïö블로블로그그ü"%string) ("ÄËÏÖ블로블로그그Ü"%string).
Proof.
  unfold solve_spec.
  vm_compute.
  reflexivity.
Qed.