requires "hcs.k"

module MINTABLE-SPEC
imports HCS

/*
  Mint

  Pre-conditions
      * Owner != 0x // constructor has been called
      * caller = SupplyManager || caller = Owner
      * value >= 0
      * TotalSupply + value <= MAX_INT // prevents overflow
      * TotalSupply >= Balances[SupplyManager]

  Post-conditions
      * TotalSupply’ = TotalSupply + value // the new supply is increased by value
      * Balances[SupplyManager]’ = Balances[SupplyManager] + value

  Note that according to the spec, the funds go to SupplyManager even if the caller is Owner.
*/
rule <k> mint(Value, { caller : Caller } ) => . ...</k>
     <balances> ... (SupplyManager |-> Balance => SupplyManager |-> Balance +Int Value) ...</balances>
     <tokenOwner> Owner </tokenOwner>
     <supplyManager> SupplyManager </supplyManager>
     <totalSupply> Supply => Supply +Int Value </totalSupply>
  requires Owner =/=Int 0
    andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
    andBool Value >=Int 0
    andBool Supply +Int Value <=Int MAXVALUE
    andBool Balance <=Int Supply
 
endmodule