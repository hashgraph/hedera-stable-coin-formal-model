requires "hcs.k"

module BURNABLE-SPEC
imports HCS
 
/*
  Burn
  
  Pre-conditions
      * Owner != 0x
      * caller = SupplyManager || caller = Owner
      * value >= 0
      * Balances[SupplyManager] >= value
      * TotalSupply >= Balances[SupplyManager]

  Post-conditions
      * TotalSupply’ = TotalSupply - value // the new supply is decreased by value
      * Balances[SupplyManager]’ = Balances[SupplyManager] - value
 */
rule <k> burn(Value, { caller : Caller } ) => . ...</k>
     <balances> ... (SupplyManager |-> Balance => SupplyManager |-> Balance -Int Value) ...</balances>
     <tokenOwner> Owner </tokenOwner>
     <supplyManager> SupplyManager </supplyManager>
     <totalSupply> Supply => Supply -Int Value </totalSupply>
  requires Owner =/=Int 0
    andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
    andBool Value >=Int 0
    andBool Balance >=Int Value
    andBool Balance <=Int Supply

endmodule