requires "erc20.k"

module MINTABLE-SPEC
  imports ERC20

rule <k> mint(Value, { caller : Caller } ) => . ...</k>
       <account>
         <id> SupplyManager </id> 
         <balance> Balance => Balance +Int Value </balance>
       </account>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
       <totalSupply> Supply => Supply +Int Value </totalSupply>
    requires 
      Owner =/=Int 0
        andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
        andBool Value >=Int 0
        andBool Supply +Int Value <=Int MAXVALUE
 
endmodule