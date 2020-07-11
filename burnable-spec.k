requires "erc20.k"

module BURNABLE-SPEC
  imports ERC20

  rule <k> burn(Value, {caller: Caller}) => . ...</k>
       <totalSupply> Supply => Supply -Int Value </totalSupply>
        <account>
         <id> SupplyManager </id> 
         <balance> Balance => Balance -Int Value </balance>
       </account>
       <tokenOwner> Owner </tokenOwner>
       <supplyManager> SupplyManager </supplyManager>
    requires 
      Balance >=Int Value
      andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
      andBool Value >=Int 0
 
endmodule