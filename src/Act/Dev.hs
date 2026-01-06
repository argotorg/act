module Act.Dev where


import Act.CLI
import Act.Coq (coq)
import Act.Bounds

import qualified Data.Text as T
import Data.Bifunctor

-- writeCoqFile :: FilePath -> FilePath -> IO ()
-- writeCoqFile src trg = do
--     contents <- readFile src
--     proceed contents (addBounds <$> compile contents) $ \claims ->
--       writeFile trg . T.unpack $ coq claims
