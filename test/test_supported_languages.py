import unittest

import main
from main import LangEntry


APP_CODES = set(
    "ar be bg ca cs da de el en es et fi fr he hi hr hu id it ja ko la lt ms nl no pl pt ro ru sk sr sv tr uk".split()
)


def kaikki(name):
    return LangEntry(name, name, 1000, "kaikki", None)


def custom(code):
    return LangEntry(f"Custom {code}", f"custom:{code}", 0, "custom", "https://x/words.txt")


class SupportedLanguagesTest(unittest.TestCase):
    def test_the_codes_are_exactly_the_ones_the_app_has_a_layout_for(self):
        self.assertEqual(APP_CODES, main.supported_codes())

    def test_only_supported_kaikki_languages_are_kept(self):
        kept, _ = main.filter_supported([kaikki("Russian"), kaikki("Klingon"), kaikki("Thai")])
        self.assertEqual(["Russian"], [l.name for l in kept])

    def test_custom_sources_are_kept_by_language_code(self):
        kept, _ = main.filter_supported([custom("tr"), custom("tlh")])
        self.assertEqual(["custom:tr"], [l.folder for l in kept])

    def test_a_supported_name_missing_from_kaikki_is_reported(self):
        _, missing = main.filter_supported([kaikki("Russian")])
        self.assertIn("Serbo-Croatian", missing)
        self.assertNotIn("Russian", missing)

    def test_serbo_croatian_gets_an_entry_for_both_app_codes(self):
        built = {
            "serbo-croatian": {
                "lang_key": "serbo-croatian", "lang_name": "Serbo-Croatian", "lang_code": "sr",
                "archive": "SR-kaikki.tar.gz", "sha256": "abc", "word_count": 5,
            }
        }
        result = main.with_alias_entries(built)
        codes = {e["lang_code"] for e in result.values()}
        self.assertEqual({"sr", "hr"}, codes)
        self.assertEqual({"SR-kaikki.tar.gz"}, {e["archive"] for e in result.values()})
        self.assertEqual("Croatian", result["serbo-croatian:hr"]["lang_name"])

    def test_a_language_with_one_code_gets_no_alias(self):
        built = {"russian": {"lang_key": "russian", "lang_name": "Russian", "lang_code": "ru"}}
        self.assertEqual(built, main.with_alias_entries(built))


if __name__ == "__main__":
    unittest.main()
