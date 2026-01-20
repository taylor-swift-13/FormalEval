
Definition eat_spec (number need remaining : nat) : (nat * nat) -> Prop :=
  fun result => 
    let (total_eaten, left) := result in
    if need <=? remaining then
      total_eaten = number + need /\ left = remaining - need
    else
      total_eaten = number + remaining /\ left = 0.
