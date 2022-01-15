import glob
import os
from pathlib import Path
for each in Path(".").glob("**/*.js"):
    os.remove(each)
