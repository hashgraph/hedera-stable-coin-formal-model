requires "hcs.k"

module CROSS-CUTTING-SPEC
imports HCS

// A mint followed by a burn will result in no changes to the totalSupply (disallowing overflow)
rule <k> mint(Value, {caller: Caller})
         ~>
         burn(Value, {caller: Caller}) => . ...</k>
     <balances> ... (SupplyManager |-> Balance) ... </balances>
     <tokenOwner> Owner </tokenOwner>
     <supplyManager> SupplyManager </supplyManager>
     <totalSupply> Supply </totalSupply>
  requires Owner =/=Int 0
    andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
    andBool Value >=Int 0
    andBool Supply >=Int Balance
    andBool Balance >=Int 0
    andBool Supply +Int Value <=Int MAXVALUE
 
// A burn followed by a mint will result in no changes to the totalSupply (disallowing underflow)
rule <k> burn(Value, {caller: Caller})
         ~>
         mint(Value, {caller: Caller}) => . ...</k>
     <balances> ... (SupplyManager |-> Balance) ... </balances>
     <tokenOwner> Owner </tokenOwner>
     <supplyManager> SupplyManager </supplyManager>
     <totalSupply> Supply </totalSupply>
  requires Owner =/=Int 0
    andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
    andBool Value >=Int 0
    andBool Balance >=Int Value
    andBool Supply >=Int Balance
    andBool Supply <=Int MAXVALUE
  
endmodule