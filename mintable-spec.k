// The final total supply is the sum of all mints

// kompile --backend java erc20.k
// kprove mint-spec.k

requires "erc20.k"

module MINTABLE-SPEC
  imports ERC20

rule
    <k>
        mint(Value, {caller: Owner})
      => 
        .
    ...</k>
    <tokenOwner> Owner </tokenOwner>
    <totalSupply>
      N => N +Int Value
    </totalSupply>
requires 
  Owner =/=Int 0
    andBool (Caller ==Int SupplyManager orBool Caller ==Int Owner)
    andBool Value >=Int 0
    andBool N +Int Value <=Int MAXVALUE
endmodule