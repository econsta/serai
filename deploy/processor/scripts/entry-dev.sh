#!/bin/bash

export MESSAGE_QUEUE_KEY="0000000000000000000000000000000000000000000000000000000000000000"
export MESSAGE_QUEUE_RPC="http://127.0.0.1:2287"

export DB_PATH="./bitcoin-db"
export ENTROPY="0001020304050607080910111213141516171819202122232425262728293031"
export NETWORK_RPC="http://serai:seraidex@127.0.0.1:18443"
export NETWORK="bitcoin"

serai-processor
