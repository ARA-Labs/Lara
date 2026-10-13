This is a harness check, not a task. Do exactly these steps:
1. Run `./lara-view show` and note its output.
2. Try to run `cat /etc/hostname` (it is expected to be refused).
Then reply with one fenced json block:
```json
{"show_output": "...", "cat_refused": true}
```
