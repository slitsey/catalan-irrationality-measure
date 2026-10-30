"""Compatibility entry point: every submission is preflight-first."""
from pathlib import Path
import runpy,sys
sys.argv[0]=str(Path(__file__).with_name('lane_client.py'))
runpy.run_path(sys.argv[0],run_name='__main__')
