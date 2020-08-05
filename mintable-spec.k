requires "hcs.k"

module MINTABLE-SPEC
imports HCS

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