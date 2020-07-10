/* Ahthor: Grigore Rosu
   Date 2 December 2017

   ERC20-K is a formalization of the informal ERC20 standard at
   https://github.com/ethereum/EIPs/blob/master/EIPS/eip-20-token-standard.md

   See erc20.md for comments.  */

module ERC20-SYNTAX
  imports DOMAINS-SYNTAX
  
  syntax Value   ::= Int  // this can be changed
  syntax Address ::= Int  // this can be changed
  syntax AExp ::= Value | Address
                | "totalSupply" "(" ")"
                | "balanceOf" "(" AExp ")"                       [strict]
                | "allowance" "(" AExp "," AExp ")"              [strict]
  syntax BExp ::= Bool
                | "constructor" "(" AExp "," AExp "," AExp "," AExp "," AExp "," AExp "," "{" "caller" ":" AExp "}" ")" [strict]
                | "approve" "(" AExp "," AExp ")"                [strict]
                | "transfer" "(" AExp "," AExp ")"               [strict]
                | "transferFrom" "(" AExp "," AExp "," AExp ")"  [strict]
                | "throw"
endmodule

module ERC20
  imports ERC20-SYNTAX
  imports DOMAINS

  configuration <ERC20>
                  <k> $PGM:K </k>
                  <accounts>
                    <account multiplicity="*" type="Set">
                      <id> 0 </id>
                      <balance> 0 </balance>
                    </account>
                  </accounts>
                  <allowances>
                    <allowance multiplicity="*" type="Set">
                      <owner> 0 </owner>
                      <spenders>
                        <allow multiplicity="*" type="Set">
                          <spender> 0 </spender>
                          <amount> 0 </amount>
                        </allow>
                      </spenders>
                    </allowance>
                  </allowances>
                  <tokenName> 0 </tokenName>
                  <tokenSymbol> 0 </tokenSymbol>
                  <tokenDecimal> 0 </tokenDecimal>
                  <totalSupply> 0 </totalSupply>
                  <tokenOwner> 0 </tokenOwner>
                  <supplyManager> 0 </supplyManager>
                  <assetProtectionManager> 0 </assetProtectionManager>
                </ERC20>

  syntax KResult ::= Int | Bool | String

  syntax Int ::= "MAXVALUE"  [function]
  rule MAXVALUE => 2 ^Int 256 -Int 1

// base

  rule <k> constructor(TokenNameArg, TokenSymbolArg, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } ) => . ...</k>
      <tokenName> TokenName => TokenNameArg </tokenName>
      <tokenSymbol> TokenSymbol => TokenSymbolArg </tokenSymbol>
      <tokenDecimal> TokenDecimal => TokenDecimalArg </tokenDecimal>
      <totalSupply> TotalSupply => TotalSupplyArg </totalSupply>
      <tokenOwner> TokenOwner => Caller </tokenOwner>
      <supplyManager> SupplyManager => SupplyManagerArg </supplyManager>
      <assetProtectionManager> AssetProtectionManager => AssetProtectionManagerArg </assetProtectionManager>
  requires TokenOwner ==Int 0
      andBool TokenDecimalArg >=Int 0
      andBool TotalSupplyArg >=Int 0
      andBool Caller =/=Int 0
      andBool SupplyManagerArg =/=Int 0
      andBool AssetProtectionManagerArg =/=Int 0

  // constructor throws if it's called more than once or arguments are incorrect
  rule <k> constructor(TokenNameArg, TokenSymbolArg, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } ) => throw ...</k>
      <tokenOwner> TokenOwner </tokenOwner>
  requires notBool (TokenOwner ==Int 0
      andBool TokenDecimalArg >=Int 0
      andBool TotalSupplyArg >=Int 0
      andBool Caller =/=Int 0
      andBool SupplyManagerArg =/=Int 0
      andBool AssetProtectionManagerArg =/=Int 0)
 
// getters

  rule <k> totalSupply() => Total ...</k>
      <totalSupply> Total </totalSupply>
      
rule <k> balanceOf(Id) => Value ...</k>
      <id> Id </id>
      <balance> Value </balance>

endmodule
