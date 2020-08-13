requires "hcs.k"

module BASE-SPEC
imports HCS

/*
  Constructor initializes the token contract.

  Pre-conditions
      * Owner = 0x // the existing Owner has not been set
      * tokenDecimal >= 0
      * totalSupply >= 0
      * caller != 0x // the newly created Owner is non-zero
      * supplyManager != 0x
      * assetProtectionManager != 0x

  Post-conditions
      * TokenName = tokenName
      * TokenSymbol = tokenSymbol
      * TokenDecimal = tokenDecimal
      * TotalSupply = totalSupply
      * Owner = caller
      * SupplyManager = supplyManager
      * AssetProtectionManager = assetProtectionManager
      * Balances = { SupplyManager->TotalSupply } // SupplyManager gets the TotalSupply of tokens
      * Allowances = {}
      * Frozen = {} // no account is frozen by default
      * KycPassed = { Owner->true, SupplyManager->true, AssetProtectionManager->true }
      * ProposedOwner = 0x
 */
rule <k> constructor(TokenNameArg, TokenSymbolArg, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } ) =>  . ...</k>
     <balances> Balances:Map => Balances [SupplyManagerArg <- TotalSupplyArg][Caller <- 0][AssetProtectionManagerArg <- 0] </balances>
     <kycpassed> KycPassed:Map => KycPassed[Caller <- true][SupplyManagerArg <- true][AssetProtectionManagerArg <- true] </kycpassed>
     <frozen> Frozen:Map => Frozen[Caller <- false][SupplyManagerArg <- false][AssetProtectionManagerArg <- false] </frozen>
     <allowances> 
        (.Bag =>
          <allowance>
            <allower> Caller </allower>
            <spenders> (0 |-> 0) </spenders>
          </allowance>
          <allowance>
            <allower> SupplyManagerArg </allower>
             <spenders> (0 |-> 0) </spenders>
           </allowance>
           <allowance>
             <allower> AssetProtectionManagerArg </allower>
             <spenders> (0 |-> 0) </spenders>
           </allowance>
        )
     </allowances>
     <tokenName> _ => TokenNameArg </tokenName>
     <tokenSymbol> _ => TokenSymbolArg </tokenSymbol>
     <tokenDecimal> _ => TokenDecimalArg </tokenDecimal>
     <totalSupply> _ => TotalSupplyArg </totalSupply>
     <tokenOwner> 0 => Caller </tokenOwner>
     <supplyManager> _ => SupplyManagerArg </supplyManager>
     <assetProtectionManager> _ => AssetProtectionManagerArg </assetProtectionManager>
     <proposedOwner> 0 </proposedOwner>
  requires TokenDecimalArg >=Int 0
      andBool TotalSupplyArg >=Int 0
      andBool Caller =/=Int 0
      andBool SupplyManagerArg =/=Int 0
      andBool AssetProtectionManagerArg =/=Int 0

// If the TokenOwner has already been set, the constructor should throw.
rule <k> constructor(_:Int, _:Int, _:Int, _:Int, _:Int, _:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
requires TokenOwner =/=Int 0
  andBool Caller =/=Int 0

// If the constructor is called twice in a row, the resulting state will only reflect the state change after the first call
// since the second call throws.
rule <k> constructor(TokenNameArg, TokenSymbolArg, TokenDecimalArg, TotalSupplyArg, SupplyManagerArg, AssetProtectionManagerArg, { caller : Caller } )
         ~>
         constructor(_:Int, _:Int, _:Int, _:Int, _:Int, _:Int, { caller : _:Int } ) => throw ...</k>
     <balances> Balances:Map => Balances [SupplyManagerArg <- TotalSupplyArg][Caller <- 0][AssetProtectionManagerArg <- 0] </balances>
     <kycpassed> KycPassed:Map => KycPassed[Caller <- true][SupplyManagerArg <- true][AssetProtectionManagerArg <- true] </kycpassed>
     <frozen> Frozen:Map => Frozen[Caller <- false][SupplyManagerArg <- false][AssetProtectionManagerArg <- false] </frozen>
     <allowances> 
        (.Bag =>
          <allowance>
            <allower> Caller </allower>
            <spenders> (0 |-> 0) </spenders>
          </allowance>
          <allowance>
            <allower> SupplyManagerArg </allower>
             <spenders> (0 |-> 0) </spenders>
           </allowance>
           <allowance>
             <allower> AssetProtectionManagerArg </allower>
             <spenders> (0 |-> 0) </spenders>
           </allowance>
        )
     </allowances>
     <tokenName> _ => TokenNameArg </tokenName>
     <tokenSymbol> _ => TokenSymbolArg </tokenSymbol>
     <tokenDecimal> _ => TokenDecimalArg </tokenDecimal>
     <totalSupply> _ => TotalSupplyArg </totalSupply>
     <tokenOwner> 0 => Caller </tokenOwner>
     <supplyManager> _ => SupplyManagerArg </supplyManager>
     <assetProtectionManager> _ => AssetProtectionManagerArg </assetProtectionManager>
     <proposedOwner> 0 </proposedOwner>
  requires TokenDecimalArg >=Int 0
      andBool TotalSupplyArg >=Int 0
      andBool Caller =/=Int 0
      andBool SupplyManagerArg =/=Int 0
      andBool AssetProtectionManagerArg =/=Int 0
 
endmodule