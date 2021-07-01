// SPDX-License-Identifier: MIT

pragma solidity ^0.5.0;

/**
 * @title PredictsStore
 * @dev Prediction data store & query
 */
contract PredictsStore {
    address private owner;
    mapping(uint256 => string) private predicts;

    /**
     * @dev Set contract deployer as owner
     */
    constructor() public {
        owner = msg.sender;
        emit OwnerSet(address(0), owner);
    }

    // event for EVM logging
    event OwnerSet(address indexed oldOwner, address indexed newOwner);

    // modifier to check if caller is owner
    modifier isOwner() {
        require(msg.sender == owner, "Caller is not owner");
        _;
    }

    // modifier to check modified
    modifier whenEmpty(uint256 key) {
        require(bytes(predicts[key]).length == 0, "Cannot be modified");
        _;
    }

    /**
     * @dev Change owner
     * @param newOwner address of new owner
     */
    function changeOwner(address newOwner) public isOwner {
        emit OwnerSet(owner, newOwner);
        owner = newOwner;
    }

    /**
     * @dev Return owner address
     * @return address of owner
     */
    function getOwner() external view returns (address) {
        return owner;
    }

    /**
     * @dev Store prediction data
     * @param key unique key
     * @param predictJson prediction data in JSON format
     */
    function addPredict(uint256 key, string memory predictJson) isOwner whenEmpty(key) public {
        predicts[key] = predictJson;
    }

    /**
     * @dev Query prediction data
     * @param key unique key
     * @return prediction data in JSON format
     */
    function getPredict(uint256 key) public view returns(string memory) {
        return predicts[key];
    }
}