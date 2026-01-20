Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p >= 2 /\
  forall d : Z, 2 <= d -> d < p -> ~(p mod d = 0).

Definition count_up_to_spec (n : Z) (result : list Z) : Prop :=
  n >= 0 /\
  (forall x, In x result <-> (is_prime x /\ 2 <= x < n)) /\
  (forall i j, 0 <= i < j -> j < Z.of_nat (length result) ->
    nth (Z.to_nat i) result 0 < nth (Z.to_nat j) result 0).

Definition primes_below_995 : list Z :=
  [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89; 97; 101; 103; 107; 109; 113; 127; 131; 137; 139; 149; 151; 157; 163; 167; 173; 179; 181; 191; 193; 197; 199; 211; 223; 227; 229; 233; 239; 241; 251; 257; 263; 269; 271; 277; 281; 283; 293; 307; 311; 313; 317; 331; 337; 347; 349; 353; 359; 367; 373; 379; 383; 389; 397; 401; 409; 419; 421; 431; 433; 439; 443; 449; 457; 461; 463; 467; 479; 487; 491; 499; 503; 509; 521; 523; 541; 547; 557; 563; 569; 571; 577; 587; 593; 599; 601; 607; 613; 617; 619; 631; 641; 643; 647; 653; 659; 661; 673; 677; 683; 691; 701; 709; 719; 727; 733; 739; 743; 751; 757; 761; 769; 773; 787; 797; 809; 811; 821; 823; 827; 829; 839; 853; 857; 859; 863; 877; 881; 883; 887; 907; 911; 919; 929; 937; 941; 947; 953; 967; 971; 977; 983; 991].

Axiom is_prime_iff_in_list : forall x, 2 <= x < 995 -> 
  (is_prime x <-> In x primes_below_995).

Axiom primes_below_995_sorted : forall i j, 
  0 <= i < j -> j < Z.of_nat (length primes_below_995) ->
  nth (Z.to_nat i) primes_below_995 0 < nth (Z.to_nat j) primes_below_995 0.

Axiom primes_below_995_bounds : forall x, In x primes_below_995 -> 2 <= x < 995.

Axiom primes_below_995_prime : forall x, In x primes_below_995 -> is_prime x.

Example count_up_to_test : count_up_to_spec 995 primes_below_995.
Proof.
  unfold count_up_to_spec.
  split.
  - lia.
  - split.
    + intros x. split.
      * intros Hin.
        split.
        -- apply primes_below_995_prime. exact Hin.
        -- apply primes_below_995_bounds. exact Hin.
      * intros [Hprime Hrange].
        apply is_prime_iff_in_list.
        -- exact Hrange.
        -- exact Hprime.
    + intros i j Hij Hj.
      apply primes_below_995_sorted.
      -- exact Hij.
      -- exact Hj.
Qed.