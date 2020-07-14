requires "erc20.k"

module MINTABLE-SPEC
  imports ERC20

rule <k> mint(Value, { caller : Caller } ) => . ...</k>
       <balances> ... (SupplyManager |-> Balance => SupplyManager |-> Balance +Int Value) ...</balances>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply => Supply +Int Value </totalSupply>
    requires 
      Owner =/=Int 0
        andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
        andBool Value >=Int 0
        andBool Supply +Int Value <=Int MAXVALUE
 
endmodule