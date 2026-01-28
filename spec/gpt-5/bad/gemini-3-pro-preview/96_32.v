Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else if n =? 2 then true
  else if n mod 2 =? 0 then false
  else
    let fix check (i : Z) (fuel : nat) {struct fuel} : bool :=
      match fuel with
      | O => true
      | S fuel' =>
          if i * i >? n then true
          else if n mod i =? 0 then false
          else check (i + 2) fuel'
      end
    in check 3 (Z.to_nat (Z.sqrt n) + 1).

Definition all_primes (n : Z) : list Z :=
  let fix aux (i : Z) (fuel : nat) {struct fuel} : list Z :=
    match fuel with
    | O => []
    | S fuel' =>
        if i >=? n then []
        else if is_prime i then i :: aux (i + 1) fuel'
        else aux (i + 1) fuel'
    end
  in aux 2 (Z.to_nat n + 1).

Example test_case: all_primes 997 = [2%Z; 3%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z; 19%Z; 23%Z; 29%Z; 31%Z; 37%Z; 41%Z; 43%Z; 47%Z; 53%Z; 59%Z; 61%Z; 67%Z; 71%Z; 73%Z; 79%Z; 83%Z; 89%Z; 97%Z; 101%Z; 103%Z; 107%Z; 109%Z; 113%Z; 127%Z; 131%Z; 137%Z; 139%Z; 149%Z; 151%Z; 157%Z; 163%Z; 167%Z; 173%Z; 179%Z; 181%Z; 191%Z; 193%Z; 197%Z; 199%Z; 211%Z; 223%Z; 227%Z; 229%Z; 233%Z; 239%Z; 241%Z; 251%Z; 257%Z; 263%Z; 269%Z; 271%Z; 277%Z; 281%Z; 283%Z; 293%Z; 307%Z; 311%Z; 313%Z; 317%Z; 331%Z; 337%Z; 347%Z; 349%Z; 353%Z; 359%Z; 367%Z; 373%Z; 379%Z; 383%Z; 389%Z; 397%Z; 401%Z; 409%Z; 419%Z; 421%Z; 431%Z; 433%Z; 439%Z; 443%Z; 449%Z; 457%Z; 461%Z; 463%Z; 467%Z; 479%Z; 487%Z; 491%Z; 499%Z; 503%Z; 509%Z; 521%Z; 523%Z; 541%Z; 547%Z; 557%Z; 563%Z; 569%Z; 571%Z; 577%Z; 587%Z; 593%Z; 599%Z; 601%Z; 607%Z; 613%Z; 617%Z; 619%Z; 631%Z; 641%Z; 643%Z; 647%Z; 653%Z; 659%Z; 661%Z; 673%Z; 677%Z; 683%Z; 691%Z; 701%Z; 709%Z; 719%Z; 727%Z; 733%Z; 739%Z; 743%Z; 751%Z; 757%Z; 761%Z; 769%Z; 773%Z; 787%Z; 797%Z; 809%Z; 811%Z; 821%Z; 823%Z; 827%Z; 829%Z; 839%Z; 853%Z; 857%Z; 859%Z; 863%Z; 877%Z; 881%Z; 883%Z; 887%Z; 907%Z; 911%Z; 919%Z; 929%Z; 937%Z; 941%Z; 947%Z; 953%Z; 967%Z; 971%Z; 977%Z; 983%Z; 991%Z].
Proof.
  vm_compute.
  reflexivity.
Qed.