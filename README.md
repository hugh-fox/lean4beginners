# [Series Playlist](https://www.youtube.com/playlist?list=PLiUpWaXHLW3hxj9yMTDN0ixWm5YdYKqJU)



### Troubleshooting
If lean4 gets stuck loading for some reason, a simple way to troubleshoot is to clear the build cache. Run `lake cache clean && lake update && lake build` to rebuild from scratch. Another reason this can happen is if lean4 doesn't have enough ram (if it doesn't crash, it won't tell you and instead load forever).