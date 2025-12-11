import Collimator.Prelude

/-!
# Configuration Management with Optics

This example shows how optics simplify updating deeply nested configuration
structures, a common pattern in application development.
-/

open Collimator
open scoped Collimator.Operators

/-! ## Configuration Types -/

structure DatabaseConfig where
  host : String
  port : Nat
  username : String
  password : String
  maxConnections : Nat
  deriving Repr

structure CacheConfig where
  enabled : Bool
  ttlSeconds : Nat
  maxSize : Nat
  deriving Repr

structure LoggingConfig where
  level : String  -- "debug" | "info" | "warn" | "error"
  outputPath : Option String
  maxFileSize : Nat
  deriving Repr

structure ServerConfig where
  host : String
  port : Nat
  timeout : Nat
  deriving Repr

structure AppConfig where
  appName : String
  version : String
  database : DatabaseConfig
  cache : CacheConfig
  logging : LoggingConfig
  server : ServerConfig
  features : List String
  deriving Repr

/-! ## Lens Definitions -/

-- Database lenses
def dbHost : Lens' DatabaseConfig String := lens' (·.host) (fun c h => { c with host := h })
def dbPort : Lens' DatabaseConfig Nat := lens' (·.port) (fun c p => { c with port := p })
def dbUsername : Lens' DatabaseConfig String := lens' (·.username) (fun c u => { c with username := u })
def dbPassword : Lens' DatabaseConfig String := lens' (·.password) (fun c p => { c with password := p })
def dbMaxConns : Lens' DatabaseConfig Nat := lens' (·.maxConnections) (fun c m => { c with maxConnections := m })

-- Cache lenses
def cacheEnabled : Lens' CacheConfig Bool := lens' (·.enabled) (fun c e => { c with enabled := e })
def cacheTtl : Lens' CacheConfig Nat := lens' (·.ttlSeconds) (fun c t => { c with ttlSeconds := t })
def cacheMaxSize : Lens' CacheConfig Nat := lens' (·.maxSize) (fun c s => { c with maxSize := s })

-- Logging lenses
def logLevel : Lens' LoggingConfig String := lens' (·.level) (fun c l => { c with level := l })
def logOutput : Lens' LoggingConfig (Option String) := lens' (·.outputPath) (fun c o => { c with outputPath := o })
def logMaxSize : Lens' LoggingConfig Nat := lens' (·.maxFileSize) (fun c s => { c with maxFileSize := s })

-- Server lenses
def srvHost : Lens' ServerConfig String := lens' (·.host) (fun c h => { c with host := h })
def srvPort : Lens' ServerConfig Nat := lens' (·.port) (fun c p => { c with port := p })
def srvTimeout : Lens' ServerConfig Nat := lens' (·.timeout) (fun c t => { c with timeout := t })

-- Top-level config lenses
def appName : Lens' AppConfig String := lens' (·.appName) (fun c n => { c with appName := n })
def appVersion : Lens' AppConfig String := lens' (·.version) (fun c v => { c with version := v })
def database : Lens' AppConfig DatabaseConfig := lens' (·.database) (fun c d => { c with database := d })
def cache : Lens' AppConfig CacheConfig := lens' (·.cache) (fun c ch => { c with cache := ch })
def logging : Lens' AppConfig LoggingConfig := lens' (·.logging) (fun c l => { c with logging := l })
def server : Lens' AppConfig ServerConfig := lens' (·.server) (fun c s => { c with server := s })
def features : Lens' AppConfig (List String) := lens' (·.features) (fun c f => { c with features := f })

/-! ## Composed Paths -/

-- Deep paths into the config
def databaseHost : Lens' AppConfig String := database ∘ dbHost
def databasePort : Lens' AppConfig Nat := database ∘ dbPort
def cacheIsEnabled : Lens' AppConfig Bool := cache ∘ cacheEnabled
def loggingLevel : Lens' AppConfig String := logging ∘ logLevel
def serverPort : Lens' AppConfig Nat := server ∘ srvPort

-- Path to optional log output
open Collimator.Instances.Option in
def logOutputPath : AffineTraversal' AppConfig String := logging ∘ logOutput ∘ somePrism' String

/-! ## Sample Configuration -/

def defaultConfig : AppConfig := {
  appName := "MyApp"
  version := "1.0.0"
  database := {
    host := "localhost"
    port := 5432
    username := "app_user"
    password := "secret123"
    maxConnections := 10
  }
  cache := {
    enabled := true
    ttlSeconds := 3600
    maxSize := 1000
  }
  logging := {
    level := "info"
    outputPath := some "/var/log/myapp.log"
    maxFileSize := 10485760  -- 10 MB
  }
  server := {
    host := "0.0.0.0"
    port := 8080
    timeout := 30
  }
  features := ["auth", "api", "websocket"]
}

/-! ## Configuration Transformations -/

/-- Apply development environment settings -/
def applyDevConfig (config : AppConfig) : AppConfig :=
  config
    & databaseHost .~ "localhost"
    & databasePort .~ 5432
    & loggingLevel .~ "debug"
    & cacheIsEnabled .~ false
    & serverPort .~ 3000

/-- Apply production environment settings -/
def applyProdConfig (config : AppConfig) : AppConfig :=
  config
    & databaseHost .~ "db.production.internal"
    & databasePort .~ 5432
    & loggingLevel .~ "warn"
    & cacheIsEnabled .~ true
    & (cache ∘ cacheTtl) .~ 7200
    & (cache ∘ cacheMaxSize) .~ 10000
    & (server ∘ srvTimeout) .~ 60
    & (database ∘ dbMaxConns) .~ 100

/-- Scale up configuration for high load -/
def scaleUp (factor : Nat) (config : AppConfig) : AppConfig :=
  config
    & (database ∘ dbMaxConns) %~ (· * factor)
    & (cache ∘ cacheMaxSize) %~ (· * factor)
    & (server ∘ srvTimeout) %~ (· + 10)

/-- Sanitize config for logging (remove sensitive data) -/
def sanitizeForLogging (config : AppConfig) : AppConfig :=
  config
    & (database ∘ dbPassword) .~ "***"
    & (database ∘ dbUsername) .~ "***"

/-! ## Example Usage -/

def examples : IO Unit := do
  IO.println "=== Configuration Management Examples ==="
  IO.println ""

  -- View nested values
  IO.println s!"Database host: {defaultConfig ^. databaseHost}"
  IO.println s!"Cache enabled: {defaultConfig ^. cacheIsEnabled}"
  IO.println s!"Log level: {defaultConfig ^. loggingLevel}"
  IO.println ""

  -- Apply environment-specific config
  let devConfig := applyDevConfig defaultConfig
  IO.println "After applying dev config:"
  IO.println s!"  Database host: {devConfig ^. databaseHost}"
  IO.println s!"  Log level: {devConfig ^. loggingLevel}"
  IO.println s!"  Cache enabled: {devConfig ^. cacheIsEnabled}"
  IO.println s!"  Server port: {devConfig ^. serverPort}"
  IO.println ""

  let prodConfig := applyProdConfig defaultConfig
  IO.println "After applying prod config:"
  IO.println s!"  Database host: {prodConfig ^. databaseHost}"
  IO.println s!"  Log level: {prodConfig ^. loggingLevel}"
  IO.println s!"  Cache TTL: {prodConfig ^. (cache ∘ cacheTtl)}"
  IO.println s!"  Max DB connections: {prodConfig ^. (database ∘ dbMaxConns)}"
  IO.println ""

  -- Scale up
  let scaledConfig := scaleUp 3 prodConfig
  IO.println "After scaling up by 3x:"
  IO.println s!"  Max DB connections: {scaledConfig ^. (database ∘ dbMaxConns)}"
  IO.println s!"  Cache max size: {scaledConfig ^. (cache ∘ cacheMaxSize)}"
  IO.println ""

  -- Sanitize for logging
  let safeConfig := sanitizeForLogging defaultConfig
  IO.println "Sanitized for logging:"
  IO.println s!"  DB password: {safeConfig ^. (database ∘ dbPassword)}"
  IO.println s!"  DB username: {safeConfig ^. (database ∘ dbUsername)}"
  IO.println ""

  -- Access optional field
  IO.println s!"Log output path: {defaultConfig ^? logOutputPath}"

  -- Modify optional field if present
  let config2 := defaultConfig & logOutputPath %~ (· ++ ".bak")
  IO.println s!"Modified log path: {config2 ^? logOutputPath}"

-- #eval examples
