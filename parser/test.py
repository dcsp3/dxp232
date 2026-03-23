import yaml
from translate import translate_api
from printer import print_api_module  # adjust if different filename

with open("test.yaml") as f:
    spec = yaml.safe_load(f)

api = translate_api(spec)

print(print_api_module(api, "Generated.Test"))