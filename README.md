# Monstock Token
Monstock token(MON) have been depoyed by inheriting the Klaytn-based KIP7.

## Smart Contracts
#### MonstockNFT.sol
* MONToken : Monstock Token Contract
* TokenTimelock : Token Timelock Contract
#### PredictsStore.sol
* PredictsStore : Storing investment forecast information

## TokenTimelock
A token holder contract that will allow a beneficiary to extract the tokens after a given release time.
Useful for simple vesting schedules like "advisors get all of their tokens after 1 year".
```
FUNCTIONS
constructor(token_, beneficiary_, releaseTime_)

token()

beneficiary()

releaseTime()

release()
```
#### constructor(IKIP7 token_, address beneficiary_, uint256 releaseTime_)
* token_ : KIP7 basic token contract being held
* address_ : beneficiary of tokens after they are released
* releaseTime_ : timestamp when token release is enabled

#### token() : return the token being held.

#### beneficiary() : return the beneficiary of the tokens.

#### releaseTime() : return the time when the tokens are released.

#### release() : Transfers tokens held by timelock to beneficiary.

## License
MIT
