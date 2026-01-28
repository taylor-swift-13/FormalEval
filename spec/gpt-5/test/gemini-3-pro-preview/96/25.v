Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (fuel : nat) (i : Z) :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check fuel' (i + 1)
      end
    in check (Z.to_nat n) 2.

Definition count_up_to (n : Z) : list Z :=
  filter is_prime (map Z.of_nat (seq 0 (Z.to_nat n))).

Example test_case_1: count_up_to 499%Z = [2%Z; 3%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z; 19%Z; 23%Z; 29%Z; 31%Z; 37%Z; 41%Z; 43%Z; 47%Z; 53%Z; 59%Z; 61%Z; 67%Z; 71%Z; 73%Z; 79%Z; 83%Z; 89%Z; 97%Z; 101%Z; 103%Z; 107%Z; 109%Z; 113%Z; 127%Z; 131%Z; 137%Z; 139%Z; 149%Z; 151%Z; 157%Z; 163%Z; 167%Z; 173%Z; 179%Z; 181%Z; 191%Z; 193%Z; 197%Z; 199%Z; 211%Z; 223%Z; 227%Z; 229%Z; 233%Z; 239%Z; 241%Z; 251%Z; 257%Z; 263%Z; 269%Z; 271%Z; 277%Z; 281%Z; 283%Z; 293%Z; 307%Z; 311%Z; 313%Z; 317%Z; 331%Z; 337%Z; 347%Z; 349%Z; 353%Z; 359%Z; 367%Z; 373%Z; 379%Z; 383%Z; 389%Z; 397%Z; 401%Z; 409%Z; 419%Z; 421%Z; 431%Z; 433%Z; 439%Z; 443%Z; 449%Z; 457%Z; 461%Z; 463%Z; 467%Z; 479%Z; 487%Z; 491%Z].
Proof. vm_compute. reflexivity. Qed.