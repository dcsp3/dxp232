import yaml


class OpenAPILoadError(Exception):
    pass


class MultiDict(dict):
    def __init__(self, *args, **kwargs):
        self._items = []
        super().__init__(*args, **kwargs)

    def add(self, key, value):
        self._items.append((key, value))
        self[key] = value

    def items_all(self):
        return self._items


class DuplicateLoader(yaml.SafeLoader):
    pass


def construct_mapping_with_duplicates(loader, node, deep=False):
    loader.flatten_mapping(node)
    mapping = MultiDict()
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        value = loader.construct_object(value_node, deep=deep)
        mapping.add(key, value)
    return mapping


DuplicateLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,
    construct_mapping_with_duplicates
)


def load_spec(path: str) -> dict:
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = yaml.load(f, Loader=DuplicateLoader)
    except FileNotFoundError:
        raise OpenAPILoadError(f"File not found: {path}")
    except yaml.YAMLError as e:
        raise OpenAPILoadError(f"YAML parsing error: {e}")

    if not isinstance(data, dict):
        raise OpenAPILoadError("OpenAPI file must contain a top-level object.")

    return data


def basic_openapi_sanity_check(spec: dict) -> None:
    required_keys = ["openapi", "paths"]

    for key in required_keys:
        if key not in spec:
            raise OpenAPILoadError(f"Missing required OpenAPI field: '{key}'")

    if not isinstance(spec["paths"], dict):
        raise OpenAPILoadError("'paths' must be an object.")
