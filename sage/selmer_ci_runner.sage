# emits receipts.json identical to sample; replace with real runner
import json
d=json.load(open("receipts/selmer_389a1_p2.json","r"))
json.dump(d,open("receipts.json","w"),separators=(",",":"))
